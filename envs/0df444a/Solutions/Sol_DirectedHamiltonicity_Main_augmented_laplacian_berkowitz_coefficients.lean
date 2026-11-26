-- Prove2me | solution 1 for DirectedHamiltonicity.Main.augmented_laplacian_berkowitz_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:44:35.309556+00:00
-- url     : https://prove2.me/submissions/3de6d53a-2416-4b8b-b00c-46958b392f07

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_DetSum
import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_det_correct
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_bit_bounds


namespace DirectedHamiltonicity.Berkowitz
open scoped Polynomial BigOperators
open BipHamCount.Deterministic

/-- Store the first D coefficients as integers zero or one. -/
def encodeCoeffs (D : ℕ) (p : (ZMod 2)[X]) : ZPoly :=
  Array.ofFn (fun k : Fin D => ((p.coeff k.val).val : ℤ))

/-- Integer coefficient array for each matrix entry, in row-major order. -/
def matrixBuffer {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) : Array (Array ZPoly) :=
  Array.ofFn (fun i => Array.ofFn (fun j => encodeCoeffs D (A i j)))

private noncomputable def decode (v : ZPoly) :=
  ∑ t ∈ Finset.range v.size, Polynomial.monomial t (v[t]?.getD 0)
private noncomputable def reducePoly := Polynomial.mapRingHom (Int.castRingHom (ZMod 2))

private theorem decode_coeff (v : ZPoly) (k : ℕ) : (decode v).coeff k = (v[k]?).getD 0 := by
  rw [decode,Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases h : k < v.size
  · simpa [h,Finset.mem_range] using (Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr h)
       (f := fun i : ℕ => if i = k then v[i]?.getD 0 else (0:ℤ)) (by simp_all))
  · have out : v[k]? = none := getElem?_neg v k (by omega)
    simpa [out] using Finset.sum_eq_zero (s := Finset.range v.size) (f := fun i : ℕ => if i=k then v[i]?.getD 0 else (0:ℤ))
      (fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega))

private theorem encode_exact (D : ℕ) (p : (ZMod 2)[X]) (h : ∀ k, D ≤ k → p.coeff k = 0) :
    reducePoly (decode (encodeCoeffs D p)) = p := by
  ext k
  change ((decode (encodeCoeffs D p)).map (Int.castRingHom (ZMod 2))).coeff k = _
  rw [Polynomial.coeff_map,decode_coeff]
  by_cases hk : k < D
  · simp [encodeCoeffs,Array.getElem?_ofFn,hk]
  · simp [encodeCoeffs,Array.getElem?_ofFn,hk,h k (by omega)]

private theorem encodeBounds (D : ℕ) (p : (ZMod 2)[X]) (k : ℕ) :
    (((encodeCoeffs D p)[k]?).getD 0).natAbs ≤ 1 := by
  by_cases h : k < D
  · have := ZMod.val_lt (p.coeff k)
    simp only [encodeCoeffs,Array.getElem?_ofFn,dif_pos h,Option.getD_some,Int.natAbs_natCast]
    omega
  · simp [encodeCoeffs,Array.getElem?_ofFn,h]

private theorem bufferEntry {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) (i j : Fin n) :
    (((matrixBuffer D A)[i.val]?).getD #[])[j.val]?.getD #[] = encodeCoeffs D (A i j) := by
  simp [matrixBuffer,Array.getElem?_ofFn,i.isLt,j.isLt]

private theorem bufferFits {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) (ZMod 2)[X]) (i j : ℕ) :
    let a := ((((matrixBuffer D A)[i]?).getD #[])[j]?).getD #[]
    a.size ≤ D ∧ ∀ k : ℕ, ((a[k]?).getD 0).natAbs ≤ 2^D := by
  by_cases hi : i<n
  · by_cases hj : j<n
    · have exactrow := bufferEntry D A (⟨i,hi⟩ : Fin n) ⟨j,hj⟩
      dsimp only at exactrow ⊢; rw [exactrow]
      exact ⟨by simp [encodeCoeffs],fun k => (encodeBounds D _ k).trans (Nat.one_le_pow D 2 (by decide))⟩
    · simp [matrixBuffer,Array.getElem?_ofFn,hi,hj]
  · simp [matrixBuffer,Array.getElem?_ofFn,hi]

/-- Source #814's uniform polynomial bound on the arithmetic computation. -/
def timeBound (n D : ℕ) :=
  let t := D+(n+1)*(2*D+n+4)
  let p := fun l : ℕ => 1+l*(2*t+n+4)
  let g := p (n+1)+t+D+n+5
  let b := 100*(g+2)^4+8*(n+3)+16
  let h := 16*(n+3)
  (n+1)*(10*(h*(h*(h*b))))+b+b

/-- One run produces all coefficients of the determinant over F₂. The bound covers
#814's actual arithmetic routine given the materialized integer input arrays. -/
theorem determinant_coeffs {n D : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)[X])
    (sizeD : 1 ≤ D) (bounded : ∀ i j k, D ≤ k → (A i j).coeff k = 0) (s : ℕ) :
    let z := (berkowitz polyOps n (matrixBuffer D A)).run s
    (∀ k : ℕ, ((((z.1[k]?).getD 0 : ℤ) : ZMod 2)) = A.det.coeff k) ∧ z.2 ≤ s + timeBound n D := by
  let M := matrixBuffer D A
  let A' : Matrix (Fin n) (Fin n) ℤ[X] := fun i j => decode (((M[i.val]?.getD #[])[j.val]?).getD #[])
  have maps : reducePoly.mapMatrix A' = A := by
    ext i j k
    change (reducePoly (decode _)).coeff k = (A i j).coeff k
    change (reducePoly (decode ((((matrixBuffer D A)[i.val]?.getD #[])[j.val]?).getD #[]))).coeff k = _
    rw [bufferEntry,encode_exact _ _ (bounded i j)]
  have det := reducePoly.map_det A'
  rw [maps] at det
  constructor
  · intro k
    have z := berkowitz_det_correct.2 M n s k
    change _ = A'.det.coeff k at z
    rw [← det]
    change _ = (A'.det.map (Int.castRingHom (ZMod 2))).coeff k
    rw [Polynomial.coeff_map,←z]; rfl
  · exact ((berkowitz_bit_bounds n D sizeD).2 M s (bufferFits D A)).2
end DirectedHamiltonicity.Berkowitz


namespace DirectedHamiltonicity.Berkowitz
open scoped Polynomial BigOperators
open Main Main.Multidigraph BipHamCount.Deterministic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

private theorem labels_bounded (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W : ℕ) (bound : ∀ e, w e ≤ W) (k : ℕ) (hk : W < k)
    (e : {e // H.KeepArc s t S e} ⊕ H.AugArc w s t R) : (H.subXRLabel w s t S R e).coeff k = 0 := by
  classical
  cases e with
  | inl a =>
    change ((Polynomial.X : (ZMod 2)[X])^(w a.1)).coeff k = 0
    rw [Polynomial.coeff_X_pow, if_neg (by have := bound a.1; omega)]
  | inr a =>
    have member := a.2.val.property
    unfold Main.Multidigraph.incomingWeights at member
    obtain ⟨e,_,weight⟩ := Finset.mem_image.mp member
    change ((Polynomial.X : (ZMod 2)[X])^a.2.val.val).coeff k = 0
    rw [Polynomial.coeff_X_pow,if_neg (by have := bound e; omega)]

private theorem entries_bounded (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W : ℕ) (bound : ∀ e, w e ≤ W) (i j : {v // v ≠ s}) (k : ℕ) (hk : W < k) :
    ((H.augLaplacian w s t S R) i j).coeff k = 0 := by
  classical
  simp only [augLaplacian,reducedLaplacian,Matrix.submatrix_apply,laplacian]
  split <;> simp [Polynomial.finsetSum_coeff,labels_bounded H w s t S R W bound k hk]

/-- A concrete coefficient buffer, for any enumeration of the vertices other than s. -/
noncomputable def laplacianBuffer (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W n : ℕ) (order : Fin n ≃ {v // v ≠ s}) :=
  matrixBuffer (W+1) ((H.augLaplacian w s t S R).submatrix order order)

theorem laplacian_all_coefficients (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W : ℕ) (bound : ∀ e, w e ≤ W) (n : ℕ) (order : Fin n ≃ {v // v ≠ s}) (start : ℕ) :
    let z := (berkowitz polyOps n (laplacianBuffer H w s t S R W n order)).run start
    (∀ k : ℕ, ((((z.1[k]?).getD 0 : ℤ) : ZMod 2)) = (H.augLaplacian w s t S R).det.coeff k) ∧
      z.2 ≤ start + timeBound n (W+1) := by
  classical
  let A := H.augLaplacian w s t S R
  have exactrun := determinant_coeffs (D:=W+1) (A.submatrix order order) (by omega)
    (fun i j k hk => entries_bounded H w s t S R W bound (order i) (order j) k (by omega)) start
  simpa only [laplacianBuffer, A, Matrix.det_submatrix_equiv_self] using exactrun
end DirectedHamiltonicity.Berkowitz


namespace DirectedHamiltonicity.Berkowitz
open scoped Polynomial BigOperators
open Main Main.Multidigraph BipHamCount.Deterministic

variable {V E : Type} [DecidableEq V]

/-- Coefficient of one Laplacian entry from an explicit list of weighted arcs.
Each matching arc toggles the parity. Over F₂ the sign on off-diagonal entries vanishes. -/
def arcBit (src dst : E → V) (weight : E → ℕ) (u v : V) (k : ℕ) : List E → Bool
  | [] => false
  | e :: es => (decide (weight e = k ∧ (if u=v then dst e=u else src e=u ∧ dst e=v))) !=
      arcBit src dst weight u v k es

def arcBuffer {nV : ℕ} (D : ℕ) (src dst : E → V) (weight : E → ℕ) (order : Fin nV → V)
    (arcs : List E) : Array (Array ZPoly) := Array.ofFn fun i => Array.ofFn fun j =>
    Array.ofFn fun k : Fin D => (((arcBit src dst weight (order i) (order j) k.val arcs).toNat : ℕ) : ℤ)

private theorem bitAdd (a b : Bool) : ((a != b).toNat : ZMod 2) = (a.toNat : ZMod 2)+b.toNat := by
  cases a <;> cases b <;> decide

private theorem bitSum [DecidableEq E] (H : Multidigraph V E) (weight : E → ℕ) (u v : V) (k : ℕ) (L : List E)
    (h : L.Nodup) : ((arcBit H.tail H.head weight u v k L).toNat : ZMod 2) =
      ∑ e ∈ L.toFinset, (if weight e = k ∧ (if u=v then H.head e=u else H.tail e=u ∧ H.head e=v)
        then 1 else 0 : ZMod 2) := by
  induction L with
  | nil => simp [arcBit]
  | cons a L ih =>
    have h' := List.nodup_cons.mp h
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using h'.1),arcBit,bitAdd,ih h'.2]
    by_cases q : weight a = k ∧ (if u=v then H.head a=u else H.tail a=u ∧ H.head a=v) <;> simp [q]

private theorem bitCoefficient [Fintype E] [DecidableEq E] (H : Multidigraph V E) (weight : E → ℕ)
    (u v : V) (k : ℕ) (L : List E) (all : L.toFinset=Finset.univ) (nodup : L.Nodup) :
    ((arcBit H.tail H.head weight u v k L).toNat : ZMod 2) =
      ((H.laplacian (fun e => (Polynomial.X : (ZMod 2)[X])^(weight e))) u v).coeff k := by
  classical
  rw [bitSum H _ _ _ _ _ nodup,all]
  unfold laplacian
  by_cases same : u=v
  · simp only [same,if_true,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,Finset.sum_filter]
    apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp_all [eq_comm]
  · simp only [same,if_false,Polynomial.coeff_neg,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,Finset.sum_filter]
    have neg (x : ZMod 2) : -x=x := by exact ZMod.neg_eq_self_mod_two x
    rw [neg]; apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp_all [eq_comm]

/-- Integer 0/1 coefficients produced by scanning the labelled arc list. -/
theorem arcBuffer_refinement [Fintype E] [DecidableEq E] {nV D : ℕ} (H : Multidigraph V E)
    (weight : E → ℕ) (order : Fin nV → V) (L : List E) (all : L.toFinset = Finset.univ) (nodup : L.Nodup) :
    arcBuffer D H.tail H.head weight order L = matrixBuffer D
      ((H.laplacian (fun e => (Polynomial.X : (ZMod 2)[X])^(weight e))).submatrix order order) := by
  unfold arcBuffer matrixBuffer
  congr 1
  funext i
  congr 1
  funext j
  unfold encodeCoeffs
  congr 1
  funext k
  have h := bitCoefficient H weight (order i) (order j) k.val L all nodup
  have z := congrArg ZMod.val h
  cases hbit : arcBit H.tail H.head weight (order i) (order j) k.val L <;>
    simp only [hbit,Bool.toNat_false,Bool.toNat_true] at z ⊢ <;>
    change _ = ((_ : ZMod 2).val : ℤ) <;> exact_mod_cast z

end DirectedHamiltonicity.Berkowitz


namespace DirectedHamiltonicity.Berkowitz
open scoped Polynomial BigOperators
open Main Main.Multidigraph BipHamCount.Deterministic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Weights of the ordinary surviving arcs and the added labelled arcs. -/
def augWeight (H : Multidigraph V E) (w : E → ℕ) (s t : V) (S : Finset (Internal s t))
    (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) :
    ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R) → ℕ :=
  Sum.elim (fun e => w e.1) (fun a => a.2.1.1)

/-- Materialize #811's matrix from a listing of all its labelled arcs. The builder
uses only comparisons and parity toggles. This equality accounts for parallel arcs. -/
theorem concrete_matrix (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W n : ℕ) (order : Fin n ≃ {v // v ≠ s})
    (L : List ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R))
    (all : ∀ e, e ∈ L) (nodup : L.Nodup) :
    let H' := H.subXR w s t S R
    arcBuffer (W+1) H'.tail H'.head (augWeight H w s t S R) (fun i => (order i).val) L =
      laplacianBuffer H w s t S R W n order := by
  classical
  let H' := H.subXR w s t S R
  let weight := augWeight H w s t S R
  have cov : L.toFinset=Finset.univ := Finset.eq_univ_of_forall (fun e => List.mem_toFinset.mpr (all e))
  have lab : (fun e => (Polynomial.X : (ZMod 2)[X])^(weight e)) = H.subXRLabel w s t S R := by
    funext e; cases e <;> rfl
  have result := arcBuffer_refinement (D:=W+1) H' weight (fun i => (order i).val) L cov nodup
  rw [lab] at result
  exact result

/-- One concrete input construction and one actual integer Berkowitz computation
serve all requested coefficients in #811, for every number of rows. -/
theorem concrete_determinant (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W : ℕ) (bound : ∀ e, w e ≤ W) (n : ℕ) (order : Fin n ≃ {v // v ≠ s})
    (L : List ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R))
    (all : ∀ e, e ∈ L) (nodup : L.Nodup) (start : ℕ) :
    let H' := H.subXR w s t S R
    let buf := arcBuffer (W+1) H'.tail H'.head (augWeight H w s t S R) (fun i => (order i).val) L
    let z := (berkowitz polyOps n buf).run start
    (∀ k : ℕ, ((((z.1[k]?).getD 0 : ℤ) : ZMod 2)) = (H.augLaplacian w s t S R).det.coeff k) ∧
      z.2 ≤ start + timeBound n (W+1) := by
  dsimp only
  rw [concrete_matrix H w s t S R W n order L all nodup]
  exact laplacian_all_coefficients H w s t S R W bound n order start
end DirectedHamiltonicity.Berkowitz


namespace DirectedHamiltonicity.Berkowitz
open Main Main.Multidigraph BipHamCount.Deterministic CapacitatedAssort.General
open scoped Polynomial BigOperators

/-- A counted scan: one visit of a labelled arc, performing a fixed number
of equality tests and a parity toggle, costs one scan unit. -/
def scanWork {V E : Type} [DecidableEq V] (src dst : E → V) (weight : E → ℕ)
    (u v : V) (k : ℕ) : List E → Work Bool
  | [] => pure false
  | e :: L => do
    charge 1
    let rest ← scanWork src dst weight u v k L
    return (decide (weight e = k ∧ (if u = v then dst e=u else src e=u ∧ dst e=v))) != rest

private theorem scanRun {V E : Type} [DecidableEq V] (src dst : E → V) (weight : E → ℕ)
    (u v : V) (k : ℕ) (L : List E) (s : ℕ) :
    (scanWork src dst weight u v k L).run s = (arcBit src dst weight u v k L,s+L.length) := by
  induction L generalizing s with
  | nil => rfl
  | cons e L ih =>
    change ((decide _ != ((scanWork src dst weight u v k L).run (s+1)).1),
      ((scanWork src dst weight u v k L).run (s+1)).2) = _
    rw [ih]; simp [arcBit]; omega

/-- Materialize an array. Record one setup charge and one charge per stored cell. -/
def buildCells {α : Type} (n : ℕ) (f : Fin n → Work α) : Work (Array α) := do
  charge 1
  let mut a := #[]
  for i in List.finRange n do
    charge 1
    let x ← f i
    a := a.push x
  return a

private theorem buildRun {α : Type} (n : ℕ) (f : Fin n → Work α) (val : Fin n → α) (c : ℕ)
    (hf : ∀ i s, (f i).run s = (val i,s+c)) (s : ℕ) :
    (buildCells n f).run s = (Array.ofFn val,s+(1+n*(1+c))) := by
  let loop := fun (i : Fin n) (a : Array α) => do
    charge 1
    let x ← f i
    return ForInStep.yield (a.push x)
  have step (L : List (Fin n)) (a : Array α) (t : ℕ) :
      (forIn L a loop).run t = (a ++ (L.map val).toArray,t+L.length*(1+c)) := by
    induction L generalizing a t with
    | nil => simp [List.forIn_nil]; rfl
    | cons i L ih =>
      rw [List.forIn_cons]
      simp only [loop,StateT.run_bind] at *
      change (forIn L (a.push ((f i).run (t+1)).1) loop).run ((f i).run (t+1)).2 = _
      rw [hf,ih]; dsimp only
      congr 1
      · apply Array.toList_inj.mp
        simp
      · simp only [List.length_cons,Nat.succ_mul]; omega
  change (forIn (List.finRange n) #[] loop).run (s+1) = _
  rw [step]; simp [← List.ofFn_eq_map,Nat.add_assoc]

/-- Source-side preprocessing counter. There are exactly n²D scans of the arc list. -/
def prepBound (n D m : ℕ) := 1+n*(1+(1+n*(1+(1+D*(1+m)))))

def buildWork {V E : Type} [DecidableEq V] {n : ℕ} (D : ℕ) (src dst : E → V)
    (weight : E → ℕ) (order : Fin n → V) (L : List E) : Work (Array (Array ZPoly)) :=
  buildCells n fun i => buildCells n fun j => buildCells D fun k => do
    let bit ← scanWork src dst weight (order i) (order j) k.val L
    return (bit.toNat : ℤ)

theorem buildWork_run {V E : Type} [DecidableEq V] {n : ℕ} (D : ℕ) (src dst : E → V)
    (weight : E → ℕ) (order : Fin n → V) (L : List E) (s : ℕ) :
    (buildWork D src dst weight order L).run s =
      (arcBuffer D src dst weight order L, s+prepBound n D L.length) := by
  apply buildRun
  intro i q; apply buildRun
  intro j t; apply buildRun
  intro k r
  let x := (scanWork src dst weight (order i) (order j) k.val L).run r
  change ((x.1.toNat:ℤ),x.2) = _
  dsimp only [x]; rw [scanRun]

/-- The whole coefficient routine begins with an explicit arc list and returns
integer coefficients, whose parity is proved correct for every degree. -/
def compute {V E : Type} [DecidableEq V] {n : ℕ} (D : ℕ) (src dst : E → V)
    (weight : E → ℕ) (order : Fin n → V) (L : List E) : Work ZPoly := do
  let buf ← buildWork D src dst weight order L
  berkowitz polyOps n buf

theorem compute_correct {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (H : Multidigraph V E) (w : E → ℕ) (s t : V)
    (S : Finset (Internal s t)) (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (W : ℕ) (bound : ∀ e, w e ≤ W) (n : ℕ) (order : Fin n ≃ {v // v ≠ s})
    (L : List ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R))
    (all : ∀ e, e ∈ L) (nodup : L.Nodup) (start : ℕ) :
    let H' := H.subXR w s t S R
    let z := (compute (W+1) H'.tail H'.head (augWeight H w s t S R) (fun i => (order i).val) L).run start
    (∀ k : ℕ, ((((z.1[k]?).getD 0 : ℤ) : ZMod 2)) = (H.augLaplacian w s t S R).det.coeff k) ∧
      z.2 ≤ start + prepBound n (W+1) L.length + timeBound n (W+1) := by
  let H' := H.subXR w s t S R
  let weight := augWeight H w s t S R
  let f := fun i : Fin n => (order i).val
  let D := W+1
  let prepared := (buildWork D H'.tail H'.head weight f L).run start
  change (∀ k, ((((berkowitz polyOps n prepared.1).run prepared.2).1[k]?.getD 0 : ℤ) : ZMod 2) = _) ∧
    ((berkowitz polyOps n prepared.1).run prepared.2).2 ≤ _
  dsimp only [prepared]
  rw [buildWork_run]
  exact concrete_determinant H w s t S R W bound n order L all nodup _
end DirectedHamiltonicity.Berkowitz

open scoped Polynomial BigOperators
open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open BipHamCount.Deterministic CapacitatedAssort.General

theorem solution :
    ∃ solve : {V E : Type} → [DecidableEq V] → {n : ℕ} → ℕ → (E → V) → (E → V) →
        (E → ℕ) → (Fin n → V) → List E → Work ZPoly,
      ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (H : Multidigraph V E) (w : E → ℕ) (s t : V) (S : Finset (Internal s t))
        (R : (i : Internal s t) → Finset (H.incomingWeights w i.1)) (W : ℕ),
        (∀ e, w e ≤ W) → ∀ (n : ℕ) (order : Fin n ≃ {v // v ≠ s})
        (L : List ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R)),
        (∀ e, e ∈ L) → L.Nodup → ∀ start : ℕ,
        let D := W+1
        let G := H.subXR w s t S R
        let labels : ({e // H.KeepArc s t S e} ⊕ H.AugArc w s t R) → ℕ :=
          Sum.elim (fun e => w e.1) (fun a => a.2.1.1)
        let z := (solve D G.tail G.head labels (fun i => (order i).val) L).run start
        let prep := 1+n*(1+(1+n*(1+(1+D*(1+L.length)))))
        let Tbits := D+(n+1)*(2*D+n+4)
        let p := fun l : ℕ => 1+l*(2*Tbits+n+4)
        let g := p (n+1)+Tbits+D+n+5
        let b := 100*(g+2)^4+8*(n+3)+16
        let h := 16*(n+3)
        let T := (n+1)*(10*(h*(h*(h*b))))+b+b
        (∀ k : ℕ, ((((z.1[k]?).getD 0 : ℤ) : ZMod 2)) =
          (H.augLaplacian w s t S R).det.coeff k) ∧ z.2 ≤ start + prep + T := by
  refine ⟨fun {_ _} _ {_} => @DirectedHamiltonicity.Berkowitz.compute _ _ _ _,?_⟩
  intro V E _ _ _ _ H w s t S R W bound n order L all nodup start
  exact DirectedHamiltonicity.Berkowitz.compute_correct H w s t S R W bound n order L all nodup start
