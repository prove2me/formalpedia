-- Prove2me | solution 1 for DetDLP.d4b_outer_branch_exact
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:12:54.332798+00:00
-- url     : https://prove2.me/submissions/10fd1c0d-e173-49a9-bed3-e5ac373d9af6

import Definitions.Def_DetDLP_ResidualScalarOracle
import Theorems.Thm_DetDLP_residual_kronecker_digit_words
set_option autoImplicit false
-- Adapted from the accepted terminal_contraction_from_residual_scalar_words
-- proof, submission 4976ab83-8b47-4ab9-9e29-85817d1dcc05 (Bingsheng).
namespace DetDLP.DenseBinaryGrid
open Polynomial Finset
abbrev base (p : ℕ) := ZMod (2^p)
noncomputable abbrev fp (f : ℤ[X]) (p : ℕ) := f.map (Int.castRingHom (base p))
abbrev ext (f : ℤ[X]) (p : ℕ) := AdjoinRoot (fp f p)
end DetDLP.DenseBinaryGrid
namespace DetDLP.CanonicalGridCoordinates
open Polynomial Finset DenseBinaryGrid
noncomputable def normal (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (x : ext f p) : (base p)[X] :=
  AdjoinRoot.modByMonicHom (hf.map _) x
noncomputable def word (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (x : ext f p) (i : Fin f.natDegree) : ℕ :=
  ((normal f hf p x).coeff i.val).val
noncomputable def liftWord (f : ℤ[X]) (w : Fin f.natDegree→ℕ) : ℤ[X] :=
  ∑ i,monomial i.val (w i:ℤ)
theorem word_lt (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (x : ext f p) (i : Fin f.natDegree) :
    word f hf p x i<2^p := ZMod.val_lt _

theorem normalized {f : ℤ[X]} (hf : f.Monic) {p : ℕ} (hp : 0<p) (x : ext f p) :
    fp (liftWord f (word f hf p x)) p=normal f hf p x := by
  haveI : Fact (1<2^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  have degree : (normal f hf p x).degree<(f.natDegree: WithBot ℕ) := by
    obtain ⟨g,rfl⟩ := AdjoinRoot.mk_surjective x
    rw [normal,AdjoinRoot.modByMonicHom_mk,← hf.natDegree_map (Int.castRingHom (base p)),
      ← degree_eq_natDegree (hf.map (Int.castRingHom (base p))).ne_zero]
    exact degree_modByMonic_lt _ (hf.map _)
  ext d
  rw [fp,liftWord,Polynomial.map_sum,finsetSum_coeff]
  by_cases H : d<f.natDegree
  · rw [sum_eq_single (⟨d,H⟩:Fin f.natDegree)]
    · simp [word]
    · intro j _ hj; simp [coeff_monomial,show j.val≠d from fun t => hj (Fin.ext t)]
    · simp
  · rw [sum_eq_zero (fun j _ => ?_), (degree_lt_iff_coeff_zero ..).mp degree d (Nat.le_of_not_gt H)]
    simp [coeff_monomial,show j.val≠d by have := j.isLt; omega]

theorem decode {f : ℤ[X]} (hf : f.Monic) {p : ℕ} (hp : 0<p) (x : ext f p) :
    aeval (AdjoinRoot.root (fp f p)) (liftWord f (word f hf p x))=x := by
  rw [AdjoinRoot.aeval_eq_of_algebra]
  change AdjoinRoot.mk _ (fp _ p)=x
  rw [normalized hf hp]
  exact AdjoinRoot.mk_leftInverse (hf.map _) _

end DetDLP.CanonicalGridCoordinates
namespace DetDLP.IntegralJetTower
open Polynomial Finset
noncomputable abbrev F (A : Type) [CommRing A] (f : ℤ[X]) := f.map (Int.castRingHom A)
abbrev U (A : Type) [CommRing A] (f : ℤ[X]) := AdjoinRoot (F A f)
noncomputable abbrev polyZ (A : Type) [CommRing A] (f : ℤ[X]) (e : ℕ) := (X:(U A f)[X])^e
abbrev Z (A : Type) [CommRing A] (f : ℤ[X]) (e : ℕ) := AdjoinRoot (polyZ A f e)
variable {A B : Type} [CommRing A] [CommRing B] (φ : A→+*B) (f : ℤ[X]) (e : ℕ)
end DetDLP.IntegralJetTower
namespace DetDLP.IntegralJetWords
open Polynomial Finset IntegralJetTower
variable (f : ℤ[X]) (e : ℕ)
noncomputable def pack {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) : A[X] :=
  ∑ j,monomial j.val (w j)
theorem cell {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) (j : Fin n) : (pack w).coeff j.val=w j := by
  classical
  rw [pack,finsetSum_coeff,sum_eq_single j]
  · simp
  · intro i _ ne; simp [coeff_monomial,show i.val≠j.val from fun z => ne (Fin.ext z)]
  · simp
theorem short {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) : (pack w).degree<(n:WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr; intro j hj
  rw [pack,finsetSum_coeff]; apply sum_eq_zero; intro i _
  simp [coeff_monomial,show i.val≠j from by have := i.isLt; omega]
theorem normal_pack {A : Type} [CommRing A] {n : ℕ} (w : Fin n→A) :
    AdjoinRoot.modByMonicHom (monic_X_pow n) (AdjoinRoot.mk ((X:A[X])^n) (pack w))=pack w := by
  nontriviality A
  rw [AdjoinRoot.modByMonicHom_mk,modByMonic_eq_self_iff (monic_X_pow n),degree_X_pow]
  exact short w
theorem truncate {A : Type} [CommRing A] (n : ℕ) (x : AdjoinRoot ((X:A[X])^n)) :
    AdjoinRoot.mk _ (pack (fun j : Fin n => (AdjoinRoot.modByMonicHom (monic_X_pow n) x).coeff j.val))=x := by
  let h := AdjoinRoot.modByMonicHom (monic_X_pow n) x
  have eq : AdjoinRoot.mk ((X:A[X])^n) (pack (fun j : Fin n => h.coeff j.val))=AdjoinRoot.mk _ h := by
    apply AdjoinRoot.mk_eq_mk.mpr; apply X_pow_dvd_iff.mpr
    intro j hj; rw [coeff_sub,show (pack (fun i : Fin n => h.coeff i.val)).coeff j=h.coeff j from cell _ ⟨j,hj⟩,sub_self]
  exact eq.trans (AdjoinRoot.mk_leftInverse (monic_X_pow n) x)

noncomputable def inner {A : Type} [CommRing A] (w : Fin f.natDegree→ℕ) : U A f :=
  AdjoinRoot.mk _ ((CanonicalGridCoordinates.liftWord f w).map (Int.castRingHom A))
noncomputable def decode {A : Type} [CommRing A] (w : Fin e→Fin f.natDegree→ℕ) : Z A f e :=
  AdjoinRoot.mk _ (pack (fun j => inner f (A:=A) (w j)))
noncomputable def words (hf : f.Monic) (p : ℕ) (x : Z (ZMod (2^p)) f e) (j : Fin e) :=
  CanonicalGridCoordinates.word f hf p ((AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val)
theorem decode_word (hf : f.Monic) (p : ℕ) (hp : 0<p) (x : Z (ZMod (2^p)) f e) :
    decode f e (words f e hf p x)=x := by
  have eq (j : Fin e) : inner f (A:=ZMod (2^p)) (words f e hf p x j)=(AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val := by
    have hh := CanonicalGridCoordinates.decode hf hp ((AdjoinRoot.modByMonicHom (monic_X_pow e) x).coeff j.val)
    rw [AdjoinRoot.aeval_eq_of_algebra] at hh; exact hh
  simp only [decode,eq]; exact truncate _ _

end DetDLP.IntegralJetWords
namespace DetDLP.ResidualOutputCoordinate
open Polynomial
variable (ell : ℕ)
theorem low {R : Type} [CommRing R] (F : R[X]) (j : Fin ell) :
    (F %ₘ ((X:R[X])^ell)).coeff j.val=F.coeff j.val := by
  rw [modByMonic_eq_sub_mul_div,coeff_sub]
  have zero : (((X:R[X])^ell)*(F /ₘ (X^ell))).coeff j.val=0 := by
    rw [mul_comm]; exact coeff_mul_X_pow' .. |>.trans (if_neg (Nat.not_le_of_lt j.isLt))
  rw [zero,sub_zero]
end DetDLP.ResidualOutputCoordinate
namespace DetDLP.TerminalKronecker
open Polynomial Finset
open scoped Polynomial

variable {R : Type*} [CommRing R]

def Width (P : Polynomial (Polynomial R)) (d : ℕ) : Prop :=
  ∀ j, (P.coeff j).natDegree ≤ d

theorem width_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial R)) (d : ℕ)
    (hf : ∀ i∈s,Width (f i) d) : Width (∑ i∈s,f i) d := by
  intro j; rw [finsetSum_coeff]
  exact natDegree_sum_le_of_forall_le _ _ (fun i hi => hf i hi j)

theorem width_mul {P Q : Polynomial (Polynomial R)} {d e : ℕ}
    (hp : Width P d) (hq : Width Q e) : Width (P*Q) (d+e) := by
  intro j; rw [coeff_mul]
  apply natDegree_sum_le_of_forall_le
  exact fun x _ => natDegree_mul_le.trans (Nat.add_le_add (hp x.1) (hq x.2))

theorem width_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial R))
    (d : ℕ) (hf : ∀ i∈s,Width (f i) d) : Width (∏ i∈s,f i) (s.card*d) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j; simp [coeff_one]; split <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.succ_mul,add_comm]
    apply width_mul (hf a (by simp))
    exact ih (fun i hi => hf i (by simp [hi]))

theorem contract_width (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Polynomial (Polynomial R))
    (d : ℕ) (hT : ∀ v t,Width (T v t) d) : Width (BTNContract G T) (G.nV*d) := by
  apply width_sum
  intro x _
  simpa using width_prod (Finset.univ : Finset (Fin G.nV))
    (fun v => T v (fun i => x ((G.ports v).get i))) d (fun v _ => hT v _)

end DetDLP.TerminalKronecker
namespace DetDLP.TerminalDigitRecovery
open TerminalKronecker Polynomial Finset
open scoped Polynomial

def grid {κ ℓ : ℕ} (i : Fin (κ*ℓ)) := (finProdFinEquiv (m:=κ) (n:=ℓ)).symm i
def exponent {κ ℓ : ℕ} (K : ℕ) (i : Fin (κ*ℓ)) := (grid i).1.val+K*(grid i).2.val

noncomputable def entry {κ ℓ : ℕ} (a : Fin (κ*ℓ) → ℕ) : Polynomial (Polynomial ℤ) :=
  ∑ i, monomial (grid i).2.val (monomial (grid i).1.val ((a i):ℤ))

theorem width_entry {κ ℓ : ℕ} (a : Fin (κ*ℓ) → ℕ) : Width (entry a) (κ-1) := by
  apply width_sum
  intro s _ j
  rw [coeff_monomial]
  split
  · exact (natDegree_monomial_le _).trans (by have := (grid s).1.isLt; omega)
  · simp

end DetDLP.TerminalDigitRecovery
namespace DetDLP.ResidualDigitEvaluation
open Polynomial Finset IntegralJetTower IntegralJetWords TerminalDigitRecovery
variable (f : ℤ[X]) (ell q : ℕ)
noncomputable def innerMap : ℤ[X]→+*U (ZMod (2^q)) f :=
  (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod (2^q))))
noncomputable def fold : (ℤ[X])[X]→+*Z (ZMod (2^q)) f ell :=
  (AdjoinRoot.mk _).comp (Polynomial.mapRingHom (innerMap f q))
noncomputable def raw (x : Fin ell→Fin f.natDegree→ℕ) := pack (fun j => CanonicalGridCoordinates.liftWord f (x j))
theorem raw_fold (x : Fin ell→Fin f.natDegree→ℕ) : fold f ell q (raw f ell x)=decode f ell (A:=ZMod (2^q)) x := by
  simp only [fold,raw,decode,RingHom.comp_apply,Polynomial.coe_mapRingHom,pack,Polynomial.map_sum,Polynomial.map_monomial]
  rfl
def flat (x : Fin ell→Fin f.natDegree→ℕ) (s : Fin (f.natDegree*ell)) := x (TerminalDigitRecovery.grid s).2 (TerminalDigitRecovery.grid s).1
theorem entry_raw (x : Fin ell→Fin f.natDegree→ℕ) : entry (flat f ell x)=raw f ell x := by
  let equiv := finProdFinEquiv (m:=f.natDegree) (n:=ell)
  unfold entry raw pack CanonicalGridCoordinates.liftWord
  simp_rw [map_sum]
  calc
    _ = ∑ i : Fin f.natDegree × Fin ell,monomial i.2.val (monomial i.1.val (x i.2 i.1:ℤ)) := by
      exact (Fintype.sum_equiv equiv.symm _ _ (fun i => rfl))
    _ = _ := by rw [Fintype.sum_prod_type,sum_comm]
theorem vertex (hf : f.Monic) (hq : 0 < q) (x : Z (ZMod (2^q)) f ell) :
    fold f ell q (entry (flat f ell (words f ell hf q x)))=x := by
  rw [entry_raw,raw_fold,decode_word f ell hf q hq x]
noncomputable def cut (K ell : ℕ) (C : Fin ell→Fin K→ℤ) : (ℤ[X])[X] :=
  pack (fun j => pack (C j))
theorem cut_eq (P : (ℤ[X])[X]) (K : ℕ) (h : TerminalKronecker.Width P (K-1)) (hk : 0 < K) :
    fold f ell q P=fold f ell q (cut K ell (fun j i => (P.coeff j.val).coeff i.val)) := by
  have restore (j : Fin ell) : pack (fun i : Fin K => (P.coeff j.val).coeff i.val)=P.coeff j.val := by
    ext i; by_cases small : i<K
    · exact cell _ ⟨i,small⟩
    · have l := short (fun i : Fin K => (P.coeff j.val).coeff i.val)
      have L := (degree_lt_iff_coeff_zero ..).mp l i (Nat.le_of_not_gt small)
      have H : (P.coeff j.val).natDegree ≤ K-1 := h j.val
      rw [L,coeff_eq_zero_of_natDegree_lt (by omega : (P.coeff j.val).natDegree < i)]
  unfold cut; simp_rw [restore]
  change AdjoinRoot.mk _ (P.map _)=AdjoinRoot.mk _ ((pack _).map _)
  have eq : (P.map (innerMap f q)) %ₘ ((X:(U (ZMod (2^q)) f)[X])^ell) =
      ((pack (fun j : Fin ell => P.coeff j.val)).map (innerMap f q)) %ₘ (X^ell) := by
    ext j; by_cases small : j<ell
    · rw [ResidualOutputCoordinate.low ell _ ⟨j,small⟩,ResidualOutputCoordinate.low ell _ ⟨j,small⟩,coeff_map,coeff_map,cell _ ⟨j,small⟩]
    · nontriviality U (ZMod (2^q)) f
      have z (F : (U (ZMod (2^q)) f)[X]) : (F %ₘ X^ell).coeff j=0 := by
        have d := degree_modByMonic_lt F (monic_X_pow ell)
        rw [degree_X_pow] at d
        exact (degree_lt_iff_coeff_zero ..).mp d j (Nat.le_of_not_gt small)
      rw [z,z]
  apply (AdjoinRoot.mk_leftInverse (monic_X_pow ell)).injective
  simpa only [AdjoinRoot.modByMonicHom_mk] using eq
end DetDLP.ResidualDigitEvaluation
namespace DetDLP.ResidualDigitOracle
open Finset Polynomial IntegralJetTower IntegralJetWords TerminalDigitRecovery ResidualDigitEvaluation
variable (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic)
noncomputable def entries {G : BipartiteMultigraph} (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Z (ZMod (2^q)) f ell)
    (v : Fin G.nV) (t : Fin (G.deg v)→Bool) := flat f ell (words f ell hf q (T v t))
abbrev K (G : BipartiteMultigraph) := G.nV*(f.natDegree-1)+1
abbrev precision (G : BipartiteMultigraph) (h β : ℕ) := β+G.nV*h+G.nV*Nat.clog 2 (f.natDegree*ell)+2
noncomputable def slice (G : BipartiteMultigraph) (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Z (ZMod (2^q)) f ell)
    (J h β : ℕ) (a : Fin G.nV→Fin J) (v : Fin G.nV) (t : Fin (G.deg v)→Bool) : TruncPoly (precision f ell G h β) (K f G*ell) :=
  Ideal.Quotient.mk _ (∑ s,monomial (exponent (K f G) s)
    (((entries f ell q hf T v t s) / 2^(h * (a v).val) % 2^h:ℕ):ZMod (2^precision f ell G h β)))
noncomputable def combine (G : BipartiteMultigraph) (h J : ℕ) (c : (Fin G.nV→Fin J)→Fin (K f G*ell)→ℕ) :=
  fold f ell q (cut (K f G) ell (fun j i =>
    ∑ a : Fin G.nV→Fin J,(2:ℤ)^(h*∑ v,(a v).val)*(c a ⟨i.val+K f G*j.val,by
      have H := Nat.mul_le_mul_left (K f G) j.isLt
      rw [Nat.mul_succ] at H; have := i.isLt; omega⟩:ℤ)))
theorem exact_value (G : BipartiteMultigraph) (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Z (ZMod (2^q)) f ell)
    (hq : 0 < q) (h J β : ℕ) (cover : q ≤ h*J) (edges : G.nE ≤ β)
    (w : (Fin G.nV→Fin J)→List Bool)
    (eval : ∀ a,EncodesTruncPoly (precision f ell G h β) (K f G*ell) (w a) (BTNContract G (slice f ell q hf G T J h β a))) :
    ∃ c : (Fin G.nV→Fin J)→Fin (K f G*ell)→ℕ,(∀ a,w a=encodeNatListBin (List.ofFn (c a))) ∧
      (∀ a i,c a i<2^precision f ell G h β) ∧ combine f ell q G h J c=BTNContract G T := by
  classical
  let A := entries f ell q hf T
  have small (v t s) : A v t s<2^(h*J) := by
    apply lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide) cover)
    apply CanonicalGridCoordinates.word_lt
  obtain ⟨c,words',caps,coeffs⟩ := residual_kronecker_digit_words G f.natDegree ell J h β edges A small w eval
  refine ⟨c,words',caps,?_⟩
  let F := BTNContract G (fun v t => entry (A v t))
  have deg : TerminalKronecker.Width F (K f G-1) :=
    TerminalKronecker.contract_width G _ _ (fun v t => width_entry _)
  have eq : combine f ell q G h J c=fold f ell q F := by
    rw [cut_eq f ell q F (K f G) deg (Nat.succ_pos _)]
    unfold combine
    apply congrArg (fold f ell q); apply congrArg (cut (K f G) ell)
    funext j i; exact (coeffs i j).symm
  rw [eq]
  change fold f ell q (∑ _,∏ _,_)=∑ _,∏ _,_
  simp only [map_sum,map_prod]
  apply sum_congr rfl; intro a _
  apply prod_congr rfl; intro v _
  exact vertex f ell q hf hq _
end DetDLP.ResidualDigitOracle

open Polynomial DetDLP DetDLP.ResidualScalarOracle

theorem solution (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → B f ell q) (hq : 0 < q)
    (h J β : ℕ) (cover : q ≤ h * J) (edges : G.nE ≤ β) (w : (Fin G.nV → Fin J) → List Bool)
    (eval : ∀ a, EncodesTruncPoly (precision f ell G h β) (spacing f G * ell) (w a)
      (BTNContract G (query f ell q hf G T J h β a))) :
    ∃ c : (Fin G.nV → Fin J) → Fin (spacing f G * ell) → ℕ,
      (∀ a, w a = encodeNatListBin (List.ofFn (c a))) ∧
      (∀ a i, c a i < 2 ^ precision f ell G h β) ∧ unpack f ell q G h J c = BTNContract G T :=
  DetDLP.ResidualDigitOracle.exact_value f ell q hf G T hq h J β cover edges w eval
