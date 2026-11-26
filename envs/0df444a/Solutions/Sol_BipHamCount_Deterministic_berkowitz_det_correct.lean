-- Prove2me | solution 1 for BipHamCount.Deterministic.berkowitz_det_correct
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:20:50.06678+00:00
-- url     : https://prove2.me/submissions/492d9a7d-a316-424f-874d-cbdd55b54759

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Nontriviality
import Mathlib.Algebra.Polynomial.Coeff

open Finset
namespace BerkowitzModel
variable {K : Type} [CommRing K]
def vectors (F : ℕ → ℕ → K) (n off : ℕ) : ℕ → ℕ → K
  | 0, i => F (off+1+i) off
  | l+1, i => ∑ j ∈ range n, F (off+1+i) (off+1+j) * vectors F n off l j

def column (F : ℕ → ℕ → K) (n off : ℕ) : ℕ → K
  | 0 => 1
  | 1 => -F off off
  | l+2 => -(∑ j ∈ range n, F off (off+1+j) * vectors F n off l j)

def coeffs (F : ℕ → ℕ → K) : ℕ → ℕ → ℕ → K
  | 0, _, i => if i = 0 then 1 else 0
  | n+1, off, i => ∑ j ∈ range (min i n + 1), column F n off (i-j) * coeffs F n (off+1) j

end BerkowitzModel

namespace BerkowitzModel

open CapacitatedAssort.General BipHamCount.Deterministic Finset
open scoped BigOperators

structure Post {α : Type} (p : Work α) (Q : α → Prop) : Prop where
  run : ∀ s, Q ((p.run s).1)
def Yield {α : Type} (Q : α → Prop) : ForInStep α → Prop
  | .yield x => Q x
  | .done _ => False

theorem purePost {α : Type} {Q : α → Prop} {x : α} (h : Q x) : Post (pure x) Q := ⟨fun _ => h⟩

theorem bindPost {α β : Type} {p : Work α} {f : α → Work β} {Q : α → Prop} {S : β → Prop}
    (hp : Post p Q) (hf : ∀ x, Q x → Post (f x) S) : Post (p >>= f) S :=
  ⟨fun s => (hf _ (hp.run s)).run _⟩

theorem tickPost {α : Type} {k : ℕ} {p : Work α} {Q : α → Prop} (hp : Post p Q) :
    Post (charge k >>= fun _ => p) Q := ⟨fun s => hp.run (s+k)⟩

theorem postMono {α : Type} {p : Work α} {Q S : α → Prop} (hp : Post p Q) (h : ∀ x, Q x → S x) :
    Post p S := ⟨fun s => h _ (hp.run s)⟩

theorem rangePost {α : Type} {n : ℕ} {p : ℕ → α → Work (ForInStep α)} {b : α}
    (I : ℕ → α → Prop) (h0 : I 0 b)
    (step : ∀ k < n, ∀ a, I k a → Post (p k a) (Yield (I (k+1)))) :
    Post (forIn (List.range n) b p) (I n) := by
  have aux (t len : ℕ) (a : α) (ht : t+len = n) (ha : I t a) :
      Post (forIn (List.range' t len) a p) (I n) := by
    induction len generalizing t a with
    | zero =>
      simp only [List.range'_zero,List.forIn_nil]
      exact purePost (by simpa using ht ▸ ha)
    | succ len ih =>
      rw [List.range'_succ,List.forIn_cons]
      apply bindPost (step t (by omega) a ha)
      intro z hz
      cases z with
      | done y => exact False.elim hz
      | yield y => exact ih _ _ (by omega) hz
  simpa only [List.range_eq_range'] using aux 0 n b (by omega) h0

structure RingModel {R K : Type} [CommRing K] (O : RingOps R) (v : R → K) : Prop where
  zero : v O.zero = 0
  one : v O.one = 1
  add (x y) : Post (O.add x y) (fun z => v z = v x + v y)
  mul (x y) : Post (O.mul x y) (fun z => v z = v x * v y)
  neg (x) : Post (O.neg x) (fun z => v z = -v x)

variable {R K : Type} [CommRing K] {O : RingOps R} {v : R → K}

structure Prefix (O : RingOps R) (v : R → K) (a : Array R) (n : ℕ) (f : ℕ → K) : Prop where
  size : a.size = n
  atLt : ∀ i < n, v (a[i]?.getD O.zero) = f i

omit [CommRing K] in
theorem prefixEmpty (f : ℕ → K) : Prefix O v #[] 0 f :=
  ⟨rfl,fun _ h => (Nat.not_lt_zero _ h).elim⟩

theorem prefixPush {a : Array R} {n : ℕ} {f : ℕ → K} (ha : Prefix O v a n f) {x : R} (hx : v x = f n) :
    Prefix O v (a.push x) (n+1) f := by
  refine ⟨by simp [ha.size],?_⟩
  intro i hi
  by_cases h : i < n
  · rw [Array.getElem?_push_lt (ha.size ▸ h)]
    simpa [Array.getElem?_eq_getElem (ha.size ▸ h)] using ha.atLt i h
  · have : i = n := by omega
    rw [Array.getElem?_push,ha.size,if_pos this]
    simpa [this] using hx

theorem arrayLoop {n : ℕ} {f : ℕ → K} {p : ℕ → Array R → Work (ForInStep (Array R))}
    (hs : ∀ k < n, ∀ a, Prefix O v a k f →
      Post (p k a) (Yield (fun b => Prefix O v b (k+1) f))) :
    Post (forIn (List.range n) #[] p) (fun b => Prefix O v b n f) :=
  rangePost (fun k a => Prefix O v a k f) (prefixEmpty _) hs

theorem sumLoop {n : ℕ} {f : ℕ → K} (model : RingModel O v) {p : ℕ → R → Work (ForInStep R)}
    (hs : ∀ k < n, ∀ a, Post (p k a) (Yield (fun z => v z = v a + f k))) :
    Post (forIn (List.range n) O.zero p) (fun a => v a = ∑ i ∈ range n, f i) := by
  apply rangePost (fun k a => v a = ∑ i ∈ range k, f i)
  · simpa using model.zero
  · intro k hk a ha
    apply postMono (hs k hk a)
    intro z hz
    cases z with
    | done _ => exact hz
    | yield z => simpa [Yield,Finset.sum_range_succ,← ha] using hz

end BerkowitzModel

open CapacitatedAssort.General BipHamCount.Deterministic Finset
open scoped BigOperators

namespace BerkowitzModel
variable {R K : Type} [CommRing K] {O : RingOps R} {v : R → K}

def entry (O : RingOps R) (v : R → K) (M : Array (Array R)) (i j : ℕ) : K :=
  v (((M[i]?.getD #[])[j]?).getD O.zero)

omit [CommRing K] in
theorem readPost (M : Array (Array R)) (i j : ℕ) :
    Post (matRead O M i j) (fun x => v x = entry O v M i j) := ⟨fun _ => rfl⟩

private lemma sumRow (h : RingModel O v) (M : Array (Array R)) (row off n : ℕ)
    (xs : Array R) (g : ℕ → K) (hg : Prefix O v xs n g) :
    Post (forIn (List.range n) O.zero fun j acc => do
      charge 3
      let r ← matRead O M row (off+1+j)
      let z ← O.mul r (xs[j]?.getD O.zero)
      let s ← O.add acc z
      return ForInStep.yield s)
      (fun s => v s = ∑ j ∈ range n, entry O v M row (off+1+j) * g j) := by
  apply sumLoop h
  intro j hj acc
  apply tickPost
  apply bindPost (readPost (O := O) (v := v) M row (off+1+j))
  intro r hr
  apply bindPost (h.mul r _)
  intro z hz
  apply bindPost (h.add acc z)
  intro s hs
  apply purePost
  change v s = _
  rw [hs,hz,hr,hg.atLt j hj]

private lemma conv (h : RingModel O v) (n i : ℕ) (hi : i < n+2) (t p : Array R)
    (f g : ℕ → K) (ht : Prefix O v t (n+2) f) (hp : Prefix O v p (n+1) g) :
    Post (forIn (List.range (min i n+1)) O.zero fun j acc => do
      charge 4
      let z ← O.mul (t[i-j]?.getD O.zero) (p[j]?.getD O.zero)
      let s ← O.add acc z
      return ForInStep.yield s)
      (fun s => v s = ∑ j ∈ range (min i n+1), f (i-j) * g j) := by
  apply sumLoop h
  intro j hj acc
  apply tickPost
  apply bindPost (h.mul _ _)
  intro z hz
  apply bindPost (h.add _ z)
  intro s hs
  apply purePost
  change v s = _
  rw [hs,hz,ht.atLt _ (by omega), hp.atLt _ (by omega)]

theorem coeffs_run (h : RingModel O v) (M : Array (Array R)) (n off : ℕ) :
    Post (berkCoeffs O M n off)
      (fun p => Prefix O v p (n+1) (coeffs (entry O v M) n off)) := by
  let F := entry O v M
  induction n generalizing off with
  | zero =>
    rw [berkCoeffs.eq_1]
    apply tickPost
    apply purePost
    exact prefixPush (prefixEmpty _) (by simpa [coeffs] using h.one)
  | succ n ih =>
    rw [berkCoeffs.eq_2]
    apply tickPost
    apply bindPost (ih (off+1))
    intro p hp
    apply bindPost (readPost (O := O) (v := v) M off off)
    intro a ha
    apply bindPost (h.neg a)
    intro na hna
    apply tickPost
    apply bindPost (Q := fun b => Prefix O v b n (vectors F n off 0))
    · apply arrayLoop
      intro j hj acc hac
      apply tickPost
      apply bindPost (readPost (O := O) (v := v) M (off+1+j) off)
      intro x hx
      exact purePost (prefixPush hac hx)
    intro vec hvec
    apply tickPost
    let stateInv := fun l (tv : Array R × Array R) =>
      Prefix O v tv.1 (l+2) (column F n off) ∧ (l < n → Prefix O v tv.2 n (vectors F n off l))
    apply bindPost (Q := stateInv n)
    · apply rangePost stateInv
      · constructor
        · apply prefixPush (prefixPush (prefixEmpty _) h.one)
          exact hna.trans (congrArg Neg.neg ha)
        · exact fun _ => hvec
      · intro l hl tv ht
        obtain ⟨ht, hvecL⟩ := ht
        apply tickPost
        apply bindPost (sumRow h M off off n tv.2 _ (hvecL hl))
        intro s hs
        apply bindPost (h.neg s)
        intro ns hns
        apply tickPost
        have hpushed : Prefix O v (tv.1.push ns) ((l+1)+2) (column F n off) := by
          apply prefixPush ht
          change v ns = -_
          rw [hns,hs]
        split
        next he =>
          apply tickPost
          apply bindPost (Q := fun b => Prefix O v b n (vectors F n off (l+1)))
          · apply arrayLoop
            intro i hi acc hac
            apply tickPost
            apply bindPost (sumRow h M (off+1+i) off n tv.2 _ (hvecL hl))
            intro u hu
            apply tickPost
            exact purePost (prefixPush hac hu)
          intro next hn
          exact purePost ⟨hpushed,fun _ => hn⟩
        next he =>
          exact purePost ⟨hpushed,fun h' => (he h').elim⟩
    intro tv htv
    apply tickPost
    apply bindPost (Q := fun b => Prefix O v b (n+2) (coeffs F (n+1) off))
    · apply arrayLoop
      intro i hi acc hac
      apply tickPost
      apply bindPost (conv h n i hi tv.1 p _ _ htv.1 hp)
      intro s hs
      apply tickPost
      exact purePost (prefixPush hac hs)
    intro out ho
    exact purePost ho

end BerkowitzModel

open scoped PowerSeries Polynomial
open Matrix BigOperators

namespace BerkowitzSeries

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def geom (D : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  fun i j => PowerSeries.mk (fun n => (D ^ n) i j)

noncomputable def pencil (D : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  1 - (PowerSeries.X : PowerSeries R) • (D.map PowerSeries.C)

omit [Fintype ι] in
private lemma coeff_oneMatrix (n : ℕ) (i j : ι) :
    PowerSeries.coeff n ((1 : Matrix ι ι (PowerSeries R)) i j) =
      (if n = 0 then (1 : Matrix ι ι R) i j else 0) := by
  by_cases h : i = j <;> simp [Matrix.one_apply,h,PowerSeries.coeff_one]

private lemma coeff_geom (D : Matrix ι ι R) (n : ℕ) (i j : ι) :
    PowerSeries.coeff n (geom D i j) = (D^n) i j := PowerSeries.coeff_mk _ _

lemma pencil_mul_geom (D : Matrix ι ι R) : pencil D * geom D = 1 := by
  rw [pencil, sub_mul, one_mul, Matrix.smul_mul]
  ext i j n
  change PowerSeries.coeff n (geom D i j - PowerSeries.X * (D.map PowerSeries.C * geom D) i j) = _
  rw [map_sub,coeff_geom,coeff_oneMatrix]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [Nat.succ_ne_zero,if_false,PowerSeries.coeff_succ_X_mul]
    rw [pow_succ']
    simp [Matrix.mul_apply,PowerSeries.coeff_C_mul,coeff_geom]

lemma geom_mul_pencil (D : Matrix ι ι R) : geom D * pencil D = 1 := by
  rw [pencil, mul_sub, mul_one, Matrix.mul_smul]
  ext i j n
  change PowerSeries.coeff n (geom D i j - PowerSeries.X * (geom D * D.map PowerSeries.C) i j) = _
  rw [map_sub,coeff_geom,coeff_oneMatrix]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [Nat.succ_ne_zero,if_false,PowerSeries.coeff_succ_X_mul]
    rw [pow_succ]
    simp [Matrix.mul_apply,PowerSeries.coeff_mul_C,coeff_geom]

private noncomputable abbrev pencilInvertible (D : Matrix ι ι R) : Invertible (pencil D) :=
  ⟨geom D,geom_mul_pencil D,pencil_mul_geom D⟩


lemma coe_revChar (D : Matrix ι ι R) : (D.charpolyRev : PowerSeries R) = (pencil D).det := by
  change Polynomial.coeToPowerSeries.ringHom D.charpolyRev = _
  rw [Matrix.charpolyRev, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> (simp [pencil,Matrix.map_apply,h]; exact mul_comm _ _)

noncomputable def seriesQuadratic (b c : ι → R) (D : Matrix ι ι R) : PowerSeries R :=
  ∑ i, ∑ j, PowerSeries.C (b i) * geom D i j * PowerSeries.C (c j)

lemma coeff_seriesQuadratic (b c : ι → R) (D : Matrix ι ι R) (n : ℕ) :
    PowerSeries.coeff n (seriesQuadratic b c D) = ∑ i, ∑ j, b i * (D^n) i j * c j := by
  simp [seriesQuadratic,PowerSeries.coeff_mul_C,PowerSeries.coeff_C_mul,coeff_geom]

lemma berk_block_series (a : R) (b c : ι → R) (D : Matrix ι ι R) :
    ((Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D).charpolyRev :
      PowerSeries R) = (D.charpolyRev : PowerSeries R) * (1 - PowerSeries.X * PowerSeries.C a -
      PowerSeries.X ^ 2 * seriesQuadratic b c D) := by
  classical
  let a' : Matrix Unit Unit (PowerSeries R) := fun _ _ => 1 - PowerSeries.X * PowerSeries.C a
  let b' : Matrix Unit ι (PowerSeries R) := fun _ i => -(PowerSeries.X * PowerSeries.C (b i))
  let c' : Matrix ι Unit (PowerSeries R) := fun i _ => -(PowerSeries.X * PowerSeries.C (c i))
  let : Invertible (pencil D) := pencilInvertible D
  have hm : pencil (Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D) =
      Matrix.fromBlocks a' b' c' (pencil D) := by
    ext (i|i) (j|j) <;> simp [pencil,Matrix.one_apply,Matrix.fromBlocks,Matrix.map_apply,a',b',c',Sum.elim]
  rw [coe_revChar,hm,Matrix.det_fromBlocks₂₂,coe_revChar]
  congr 1
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  change 1 - PowerSeries.X * PowerSeries.C a - (b' * geom D * c') () () = _
  congr 1
  change (∑ j, (∑ i, b' () i * geom D i j) * c' j ()) = _
  simp only [Finset.sum_mul,seriesQuadratic,Finset.mul_sum,b',c']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


/-- The left column of the Berkowitz Toeplitz matrix, continued to all orders. -/
noncomputable def toeplitzCol (a : R) (b c : ι → R) (D : Matrix ι ι R) : ℕ → R
  | 0 => 1
  | 1 => -a
  | k+2 => -(∑ i, ∑ j, b i * (D^k) i j * c j)

private lemma toeplitzCoeff (a : R) (b c : ι → R) (D : Matrix ι ι R) (k : ℕ) :
    PowerSeries.coeff k (1 - PowerSeries.X * PowerSeries.C a -
      PowerSeries.X^2 * seriesQuadratic b c D) = toeplitzCol a b c D k := by
  rw [pow_two,mul_assoc]
  cases k with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff,toeplitzCol]
  | succ k =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_one,Nat.succ_ne_zero,
      if_false,zero_sub]
    cases k with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff,toeplitzCol]
    | succ k => simp [PowerSeries.coeff_succ_X_mul,coeff_seriesQuadratic,toeplitzCol]

theorem berkowitz_recurrence (a : R) (b c : ι → R) (D : Matrix ι ι R) (k : ℕ) :
    ((Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D).charpolyRev).coeff k =
      ∑ j ∈ Finset.range (k+1), toeplitzCol a b c D (k-j) * D.charpolyRev.coeff j := by
  rw [← Polynomial.coeff_coe,berk_block_series,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_coe,toeplitzCoeff,mul_comm]

end BerkowitzSeries

namespace BerkowitzModel
open Matrix Finset BerkowitzSeries
open scoped BigOperators Matrix
variable {K : Type} [CommRing K]

def block (F : ℕ → ℕ → K) (n off : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => F (off+i) (off+j)

private def splitAtZero (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩|i) <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private lemma vec_eq (F : ℕ → ℕ → K) (n off l : ℕ) (i : Fin n) :
    vectors F n off l i =
      ((block F n (off+1))^l *ᵥ (fun j => F (off+1+j) off)) i := by
  induction l generalizing i with
  | zero => simp [vectors]
  | succ l ih =>
    rw [vectors,← Fin.sum_univ_eq_sum_range]
    rw [pow_succ',← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec,dotProduct,block]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih]
    rfl

private lemma column_toeplitz (F : ℕ → ℕ → K) (n off l : ℕ) :
    column F n off l = toeplitzCol (F off off) (fun j : Fin n => F off (off+1+j))
      (fun i : Fin n => F (off+1+i) off) (block F n (off+1)) l := by
  cases l with
  | zero => rfl
  | succ l =>
    cases l with
    | zero => rfl
    | succ l =>
      rw [column, toeplitzCol, ← Fin.sum_univ_eq_sum_range]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vec_eq]
      simp [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

private lemma border_eq (F : ℕ → ℕ → K) (n off : ℕ) :
    (block F (n+1) off).submatrix (splitAtZero n) (splitAtZero n) =
      Matrix.fromBlocks (fun _ _ : Unit => F off off) (fun _ (i : Fin n) => F off (off+1+i))
        (fun (i : Fin n) _ => F (off+1+i) off) (block F n (off+1)) := by
  ext (i|i) (j|j) <;> simp [block,Matrix.submatrix_apply,splitAtZero,Matrix.fromBlocks,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private lemma rev_sub {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (D : Matrix I I K) (e : J ≃ I) : (D.submatrix e e).charpolyRev = D.charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly]
  exact congrArg Polynomial.reverse (Matrix.charpoly_reindex e.symm D)

theorem coeffs_correct (F : ℕ → ℕ → K) (n off i : ℕ) (hi : i ≤ n) :
    coeffs F n off i = (block F n off).charpolyRev.coeff i := by
  classical
  nontriviality K
  induction n generalizing off i with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp [coeffs,Matrix.charpolyRev]
  | succ n ih =>
    rw [coeffs,← rev_sub (block F (n+1) off) (splitAtZero n), border_eq, berkowitz_recurrence]
    symm
    calc
      _ = ∑ j ∈ Finset.range (min i n+1), toeplitzCol _ _ _ (block F n (off+1)) (i-j) *
          (block F n (off+1)).charpolyRev.coeff j := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro j hj hj'
        have hjn : n < j := by simp only [Finset.mem_range] at hj hj'; omega
        have hd : (block F n (off+1)).charpolyRev.natDegree ≤ n := by
          rw [← Matrix.reverse_charpoly]
          simpa using (block F n (off+1)).charpoly.reverse_natDegree_le
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hjn),mul_zero]
      _ = _ := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [column_toeplitz,ih (off+1) j (by have := mem_range.mp hj; omega)]

theorem det_final (F : ℕ → ℕ → K) (n off : ℕ) :
    (-1 : K)^n * coeffs F n off n = (block F n off).det := by
  classical
  nontriviality K
  rw [coeffs_correct _ _ _ _ le_rfl, ← Matrix.reverse_charpoly, Polynomial.coeff_reverse,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Polynomial.revAt_le le_rfl,
    Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff,Fintype.card_fin]

end BerkowitzModel

namespace BerkowitzModel
open BipHamCount.Deterministic CapacitatedAssort.General Polynomial Finset
open scoped Polynomial

noncomputable def polyEval (a : ZPoly) : ℤ[X] :=
  ∑ i ∈ range a.size, monomial i (a[i]?.getD 0)

theorem coeff_polyEval (a : ZPoly) (i : ℕ) : (polyEval a).coeff i = a[i]?.getD 0 := by
  simp only [polyEval,finsetSum_coeff,coeff_monomial]
  by_cases hi : i < a.size
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi)]
    · simp
    · intro j _ hj; simp [hj]
  · rw [Array.getElem?_eq_none (by omega : a.size ≤ i)]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : j ≠ i := by have := Finset.mem_range.mp hj; omega
    simp [this]

private lemma coeff_fromPrefix (a : Array ℤ) (p : ℤ[X]) (d : ℕ)
    (hp : Prefix intOps id a d (fun i => p.coeff i)) (hn : ∀ i, d ≤ i → p.coeff i = 0) :
    polyEval a = p := by
  ext i
  rw [coeff_polyEval]
  by_cases hi : i < d
  · exact hp.atLt i hi
  · rw [hn i (by omega),Array.getElem?_eq_none (by have := hp.size; omega : a.size ≤ i)]; rfl

private theorem zaddPost (x y : ℤ) : Post (zadd x y) (· = x+y) := ⟨fun _ => rfl⟩
private theorem zsubPost (x y : ℤ) : Post (zsub x y) (· = x-y) := ⟨fun _ => rfl⟩
private theorem zmulPost (x y : ℤ) : Post (zmul x y) (· = x*y) := ⟨fun _ => rfl⟩

theorem integerRingModel : RingModel intOps id :=
  ⟨rfl,rfl,zaddPost,zmulPost,fun x => postMono (zsubPost 0 x) (by intro z hz; simpa using hz)⟩

theorem paddPost (a b : ZPoly) : Post (padd a b) (fun p => polyEval p = polyEval a + polyEval b) := by
  let d := max a.size b.size
  rw [padd]
  apply tickPost
  apply bindPost (Q := fun z => Prefix intOps id z d (fun i => (polyEval a + polyEval b).coeff i))
  · apply arrayLoop
    intro k hk xs hx
    apply tickPost
    apply bindPost (zaddPost _ _)
    intro x h
    apply purePost
    apply prefixPush hx
    simpa [coeff_polyEval] using h
  intro x hx
  apply purePost
  apply coeff_fromPrefix x _ d hx
  intro i hi
  have ha : a.size ≤ i := le_trans (le_max_left ..) hi
  have hb : b.size ≤ i := le_trans (le_max_right ..) hi
  simp [coeff_polyEval,Array.getElem?_eq_none ha, Array.getElem?_eq_none hb]

private lemma decode_bump (a : ZPoly) {i : ℕ} (hi : i < a.size) (v : ℤ) :
    polyEval (a.set! i ((a[i]?.getD 0)+v)) = polyEval a + monomial i v := by
  ext j
  simp only [coeff_polyEval,coeff_add,coeff_monomial,Array.set!_eq_setIfInBounds]
  by_cases h : i = j
  · subst j; rw [Array.getElem?_setIfInBounds_self_of_lt hi]; simp
  · rw [Array.getElem?_setIfInBounds_ne h]; simp [h]

private lemma decode_zeros (n : ℕ) : polyEval (Array.replicate n (0 : ℤ)) = 0 := by
  ext i
  by_cases h : i < n <;> simp [coeff_polyEval,Array.getElem?_replicate,h]

private noncomputable def factor (a : ZPoly) (i : ℕ) : ℤ[X] := monomial i (a[i]?.getD 0)

theorem pmulPost (a b : ZPoly) : Post (pmul a b) (fun c => polyEval c = polyEval a * polyEval b) := by
  rw [pmul]
  apply tickPost
  let N := a.size+b.size
  let invariant := fun k (z : ZPoly) =>
    z.size = N ∧ polyEval z = ∑ i ∈ range k, ∑ j ∈ range b.size, factor a i * factor b j
  apply bindPost (Q := invariant a.size)
  · apply rangePost invariant
    · simp [invariant,N,decode_zeros]
    · intro i hi z hz
      obtain ⟨hsize, hp⟩ := hz
      apply tickPost
      let invJ := fun k (u : ZPoly) => u.size = N ∧
        polyEval u = polyEval z + ∑ j ∈ range k, factor a i * factor b j
      apply bindPost (Q := invJ b.size)
      · apply rangePost invJ
        · simp [invJ,hsize]
        · intro j hj u hu
          obtain ⟨hus,hu⟩ := hu
          apply tickPost
          apply bindPost (zmulPost _ _)
          intro v hv
          apply bindPost (zaddPost _ _)
          intro w hw
          apply purePost
          change invJ (j+1) _
          constructor
          · simp [hus]
          · rw [hw, decode_bump _ (by dsimp [N] at hus; omega) _, hu,Finset.sum_range_succ,hv]
            simp [factor,monomial_mul_monomial,add_assoc]
      intro u hu
      apply purePost
      change invariant (i+1) u
      exact ⟨hu.1,by rw [hu.2,hp,Finset.sum_range_succ]⟩
  intro z hz
  apply purePost
  rw [hz.2]
  simp only [polyEval,factor,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm


private lemma negList (l : List ℤ) (a : Array ℤ) :
    Post (forIn l a fun x (b : Array ℤ) => do
      charge 2
      let c ← zsub 0 x
      return ForInStep.yield (b.push c))
      (fun out => out.toList = a.toList ++ l.map (-·)) := by
  induction l generalizing a with
  | nil => simp only [List.forIn_nil,List.map_nil,List.append_nil]; exact purePost rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bindPost (Q := (· = .yield (a.push (-x))))
    · apply tickPost
      apply bindPost (zsubPost _ _)
      intro c hc
      apply purePost
      simp [hc]
    intro y hy
    subst y
    apply postMono (ih _)
    intro out h
    simpa using h

theorem pnegPost (a : ZPoly) : Post (pneg a) (fun c => polyEval c = - polyEval a) := by
  rw [pneg]
  apply tickPost
  have hneg := negList a.toList #[]
  rw [Array.forIn_toList] at hneg
  apply bindPost hneg
  intro out hout
  apply purePost
  ext i
  simp only [coeff_neg,coeff_polyEval]
  have h := congrArg (fun l : List ℤ => l[i]?) hout
  simp only [Array.toList_empty,List.nil_append,Array.getElem?_toList,List.getElem?_map] at h
  rw [h]
  cases a[i]? <;> simp

theorem polyRingModel : RingModel polyOps polyEval := by
  refine ⟨?_,?_,paddPost,pmulPost,pnegPost⟩
  · simp [polyOps,polyEval]
  · simp [polyOps,polyEval,Finset.sum_range_succ]

end BerkowitzModel

open CapacitatedAssort.General BipHamCount.Deterministic Finset
open scoped BigOperators Polynomial
namespace BerkowitzModel
variable {R K : Type} [CommRing K] {O : RingOps R} {v : R → K}

theorem berkowitz_run (h : RingModel O v) (M : Array (Array R)) (n : ℕ) :
    Post (berkowitz O n M) (fun x => v x = (block (entry O v M) n 0).det) := by
  rw [berkowitz]
  apply bindPost (coeffs_run h M n 0)
  intro p hp
  apply tickPost
  have hv := hp.atLt n (by omega)
  rw [← det_final]
  split
  next he =>
    apply purePost
    have hs : Even n := Nat.even_iff.mpr he
    rw [hs.neg_one_pow,one_mul]
    exact hv
  next he =>
    apply postMono (h.neg _)
    intro x hx
    have hs : Odd n := Nat.not_even_iff_odd.mp (fun hh => he (Nat.even_iff.mp hh))
    rw [hx,hv,hs.neg_one_pow,neg_one_mul]

end BerkowitzModel
open BipHamCount.Deterministic BerkowitzModel
open scoped BigOperators Polynomial
theorem solution :
    (∀ (M : Array (Array ℤ)) (n s : ℕ),
      let A : Matrix (Fin n) (Fin n) ℤ :=
        fun i j => ((M[i.val]?.getD #[])[j.val]?).getD 0
      ((berkowitz intOps n M).run s).1 = A.det) ∧
    (∀ (M : Array (Array ZPoly)) (n s k : ℕ),
      let decode := fun a : ZPoly => ∑ t ∈ Finset.range a.size,
        Polynomial.monomial t (a[t]?.getD 0)
      let A : Matrix (Fin n) (Fin n) ℤ[X] :=
        fun i j => decode (((M[i.val]?.getD #[])[j.val]?).getD #[])
      ((((berkowitz polyOps n M).run s).1)[k]?).getD 0 = A.det.coeff k) := by
  constructor
  · intro M n s
    have he : block (entry intOps id M) n 0 =
        (fun i j : Fin n => ((M[i.val]?.getD #[])[j.val]?).getD 0) := by
      ext i j
      change ((M[0+i.val]?.getD #[])[0+j.val]?).getD 0 = _
      simp
    rw [← he]
    exact (berkowitz_run integerRingModel M n).run s
  · intro M n s k
    let A : Matrix (Fin n) (Fin n) ℤ[X] :=
      fun i j => polyEval (((M[i.val]?.getD #[])[j.val]?).getD #[])
    have he : block (entry polyOps polyEval M) n 0 = A := by
      apply Matrix.ext
      intro i j
      change polyEval (((M[0+i.val]?.getD #[])[0+j.val]?).getD #[]) = _
      simp [A]
    have hd := (berkowitz_run polyRingModel M n).run s
    change polyEval _ = (block _ _ _).det at hd
    rw [he] at hd
    change _ = A.det.coeff k
    rw [← hd,coeff_polyEval]
