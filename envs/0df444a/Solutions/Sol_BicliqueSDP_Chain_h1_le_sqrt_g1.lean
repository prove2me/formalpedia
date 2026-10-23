-- Prove2me | solution 1 for BicliqueSDP.Chain.h1_le_sqrt_g1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:39:48.016994+00:00
-- url     : https://prove2.me/submissions/bf542a4f-e4e4-45c7-b8cd-450622e72ce7

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



namespace BicliqueSDP.Chain.R6

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A zero diagonal entry of a real PSD matrix forces its entire row to vanish. -/
theorem entry_eq_zero_of_diag_eq_zero {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    {i : ι} (hii : X i i = 0) (j : ι) : X i j = 0 := by
  have hz : X *ᵥ Pi.single i 1 = 0 :=
    (hX.dotProduct_mulVec_zero_iff _).mp (by simpa [mulVec_single_one] using hii)
  have hji : X j i = 0 := by
    simpa [mulVec_single_one] using congrFun hz j
  simpa [hji] using (hX.isHermitian.apply i j).symm

/-- A row with zero diagonal contributes zero to every matrix-vector product. -/
theorem mulVec_eq_zero_of_diag_eq_zero {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    {i : ι} (hii : X i i = 0) (u : ι → ℝ) : (X *ᵥ u) i = 0 := by
  simp [mulVec, dotProduct, entry_eq_zero_of_diag_eq_zero hX hii]

/-- The diagonal scaling associated with a vector and a PSD matrix. -/
def liftWeight (X : Matrix ι ι ℝ) (u : ι → ℝ) (i : ι) : ℝ :=
  (X *ᵥ u) i / X i i

/-- The lower-right block obtained by diagonal congruence. -/
def genericLiftMatrix (X : Matrix ι ι ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => liftWeight X u i * liftWeight X u j * X i j

/-- The top-left entry of the unnormalized lift. -/
def liftValue (X : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ :=
  u ⬝ᵥ (X *ᵥ u)

omit [DecidableEq ι] in
lemma liftValue_nonneg {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (u : ι → ℝ) :
    0 ≤ liftValue X u := by
  simpa [liftValue] using hX.dotProduct_mulVec_nonneg u

omit [DecidableEq ι] in
lemma mulVec_eq_zero_of_liftValue_eq_zero {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (u : ι → ℝ) (hu : liftValue X u = 0) : X *ᵥ u = 0 := by
  apply (hX.dotProduct_mulVec_zero_iff u).mp
  simpa [liftValue] using hu

/-- The unnormalized bordered matrix associated with a vector. -/
def rawLift (X : Matrix ι ι ℝ) (u : ι → ℝ) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  Matrix.fromBlocks (fun _ _ => liftValue X u)
    (fun _ j => genericLiftMatrix X u j j) (fun i _ => genericLiftMatrix X u i i) (genericLiftMatrix X u)

lemma liftWeight_mul_diag {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (u : ι → ℝ) (i : ι) : liftWeight X u i * X i i = (X *ᵥ u) i := by
  by_cases hii : X i i = 0
  · simp [liftWeight, hii, mulVec_eq_zero_of_diag_eq_zero hX hii u]
  · exact div_mul_cancel₀ _ hii

omit [DecidableEq ι] in
lemma liftWeight_mul_mulVec (X : Matrix ι ι ℝ) (u : ι → ℝ) (i : ι) :
    liftWeight X u i * (X *ᵥ u) i = genericLiftMatrix X u i i := by
  by_cases hii : X i i = 0
  · simp [liftWeight, genericLiftMatrix, hii]
  · dsimp [liftWeight, genericLiftMatrix]
    field_simp

/-- The rectangular congruence matrix used to construct the lift. -/
def liftFactor (X : Matrix ι ι ℝ) (u : ι → ℝ) : Matrix (Unit ⊕ ι) ι ℝ :=
  Matrix.fromRows (fun _ : Unit => u) (Matrix.diagonal (liftWeight X u))

set_option backward.isDefEq.respectTransparency false in
lemma liftFactor_congruence {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (u : ι → ℝ) :
    liftFactor X u * X * (liftFactor X u)ᵀ = rawLift X u := by
  have hsym (i j : ι) : X i j = X j i := by
    simpa using (hX.isHermitian.apply i j).symm
  rw [Matrix.mul_assoc]
  ext (i | i) (j | j)
  · simp [liftFactor, rawLift, liftValue, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp only [liftFactor, rawLift, fromBlocks_apply₁₂, Matrix.mul_apply,
      transpose_apply, fromRows_apply_inl, fromRows_apply_inr, diagonal_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← liftWeight_mul_mulVec]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsym k j]
    ring
  · simp only [liftFactor, rawLift, fromBlocks_apply₂₁, Matrix.mul_apply,
      transpose_apply, fromRows_apply_inl, fromRows_apply_inr, diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact liftWeight_mul_mulVec X u i
  · simp only [liftFactor, rawLift, fromBlocks_apply₂₂, Matrix.mul_apply,
      transpose_apply, fromRows_apply_inr, diagonal_apply,
      mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, genericLiftMatrix]
    ring

/-- The raw bordered lift is positive semidefinite. -/
theorem rawLift_posSemidef {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (u : ι → ℝ) :
    (rawLift X u).PosSemidef := by
  rw [← liftFactor_congruence hX u]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    hX.mul_mul_conjTranspose_same (liftFactor X u)

set_option backward.isDefEq.respectTransparency false in
/-- Normalizing the sum of two raw lifts produces a feasible bordered PSD matrix. -/
theorem bordered_sum_lift_posSemidef {κ : Type} [Fintype κ] [DecidableEq κ]
    {X : Matrix κ κ ℝ} (hX : X.PosSemidef) (u v : κ → ℝ)
    (ht : 0 < liftValue X u + liftValue X v) :
    (bordered ((liftValue X u + liftValue X v)⁻¹ •
      (genericLiftMatrix X u + genericLiftMatrix X v))).PosSemidef := by
  have heq : bordered ((liftValue X u + liftValue X v)⁻¹ •
      (genericLiftMatrix X u + genericLiftMatrix X v)) =
      (liftValue X u + liftValue X v)⁻¹ • (rawLift X u + rawLift X v) := by
    ext (i | i) (j | j) <;>
      simp [bordered, rawLift, Matrix.fromBlocks, ne_of_gt ht, mul_add]
  rw [heq]
  exact ((rawLift_posSemidef hX u).add (rawLift_posSemidef hX v)).smul
    (inv_nonneg.mpr ht.le)

end

end BicliqueSDP.Chain.R6


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BicliqueSDP.Chain.R6

open Matrix

noncomputable section

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

abbrev leftSum (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (i : V1 ⊕ V2) : ℝ :=
  ∑ j : V1, X i (Sum.inl j)

abbrev rightSum (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (i : V1 ⊕ V2) : ℝ :=
  ∑ j : V2, X i (Sum.inr j)

abbrev leftScale (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (i : V1 ⊕ V2) : ℝ :=
  leftSum X i / X i i

abbrev rightScale (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (i : V1 ⊕ V2) : ℝ :=
  rightSum X i / X i i

def liftMatrix (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ :=
  fun i j => X i j * (leftScale X i * leftScale X j + rightScale X i * rightScale X j)

def liftMass (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) : ℝ :=
  (∑ i : V1, leftSum X (Sum.inl i)) + ∑ j : V2, rightSum X (Sum.inr j)

lemma frob_Cmat_eq_cross (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : X.IsSymm) : frob Cmat X = ∑ i : V1, ∑ j : V2, X (Sum.inl i) (Sum.inr j) := by
  have hsym (i : V1) (j : V2) : X (Sum.inr j) (Sum.inl i) = X (Sum.inl i) (Sum.inr j) :=
    hX.apply _ _
  simp [frob, Fintype.sum_sum_type, Cmat, Matrix.fromBlocks]
  simp_rw [hsym]
  rw [Finset.sum_comm (f := fun j : V2 => fun i : V1 => (2⁻¹ : ℝ) * X (Sum.inl i) (Sum.inr j))]
  simp_rw [← Finset.mul_sum]
  ring

lemma liftMatrix_isSymm (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : X.IsSymm) :
    (liftMatrix X).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [liftMatrix, hX.apply i j]
  ring

lemma liftMatrix_vanishes (E : V1 → V2 → Prop)
    (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : VanishesOnEdges E X) :
    VanishesOnEdges E (liftMatrix X) := by
  intro i j hij
  simp [liftMatrix, hX i j hij]

lemma leftScale_mul_diag (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hzero : ∀ i, X i i = 0 → ∀ j, X i j = 0) (i : V1 ⊕ V2) :
    leftScale X i * X i i = leftSum X i := by
  by_cases hd : X i i = 0
  · simp [leftScale, leftSum, hd, hzero i hd]
  · exact div_mul_cancel₀ _ hd

lemma rightScale_mul_diag (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hzero : ∀ i, X i i = 0 → ∀ j, X i j = 0) (i : V1 ⊕ V2) :
    rightScale X i * X i i = rightSum X i := by
  by_cases hd : X i i = 0
  · simp [rightScale, rightSum, hd, hzero i hd]
  · exact div_mul_cancel₀ _ hd

lemma liftMatrix_cross (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : X.IsSymm) (hzero : ∀ i, X i i = 0 → ∀ j, X i j = 0) (h : ℝ)
    (hleft : ∀ i : V1, rightSum X (Sum.inl i) = 2 * h * X (Sum.inl i) (Sum.inl i))
    (hright : ∀ j : V2, leftSum X (Sum.inr j) = 2 * h * X (Sum.inr j) (Sum.inr j))
    (i : V1) (j : V2) :
    liftMatrix X (Sum.inl i) (Sum.inr j) =
      2 * h * (X (Sum.inl i) (Sum.inr j) * leftScale X (Sum.inl i) +
        X (Sum.inl i) (Sum.inr j) * rightScale X (Sum.inr j)) := by
  by_cases hi : X (Sum.inl i) (Sum.inl i) = 0
  · simp [liftMatrix, hzero _ hi]
  by_cases hj : X (Sum.inr j) (Sum.inr j) = 0
  · have hz : X (Sum.inl i) (Sum.inr j) = 0 := by
      rw [← hX.apply (Sum.inl i) (Sum.inr j)]
      exact hzero _ hj _
    simp [liftMatrix, hz]
  have hi' : rightScale X (Sum.inl i) = 2 * h := by
    unfold rightScale
    rw [hleft i, mul_div_cancel_right₀ _ hi]
  have hj' : leftScale X (Sum.inr j) = 2 * h := by
    unfold leftScale
    rw [hright j, mul_div_cancel_right₀ _ hj]
  simp only [liftMatrix, hi', hj']
  ring

lemma liftMatrix_objective (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : X.IsSymm) (hzero : ∀ i, X i i = 0 → ∀ j, X i j = 0) (h : ℝ)
    (hleft : ∀ i : V1, rightSum X (Sum.inl i) = 2 * h * X (Sum.inl i) (Sum.inl i))
    (hright : ∀ j : V2, leftSum X (Sum.inr j) = 2 * h * X (Sum.inr j) (Sum.inr j)) :
    frob Cmat (liftMatrix X) = 4 * h ^ 2 * liftMass X := by
  have hL : (∑ i : V1, ∑ j : V2, X (Sum.inl i) (Sum.inr j) * leftScale X (Sum.inl i)) =
      2 * h * ∑ i : V1, leftSum X (Sum.inl i) := by
    calc
      _ = ∑ i : V1, rightSum X (Sum.inl i) * leftScale X (Sum.inl i) := by
        simp only [rightSum, Finset.sum_mul]
      _ = ∑ i : V1, 2 * h * leftSum X (Sum.inl i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hleft i, ← leftScale_mul_diag X hzero]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hR : (∑ i : V1, ∑ j : V2, X (Sum.inl i) (Sum.inr j) * rightScale X (Sum.inr j)) =
      2 * h * ∑ j : V2, rightSum X (Sum.inr j) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : V2, leftSum X (Sum.inr j) * rightScale X (Sum.inr j) := by
        simp only [leftSum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hX.apply (Sum.inl i) (Sum.inr j)]
      _ = ∑ j : V2, 2 * h * rightSum X (Sum.inr j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hright j, ← rightScale_mul_diag X hzero]
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [frob_Cmat_eq_cross _ (liftMatrix_isSymm X hX)]
  simp_rw [liftMatrix_cross X hX hzero h hleft hright]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hL, hR]
  unfold liftMass
  ring


def leftIndicator : V1 ⊕ V2 → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)

def rightIndicator : V1 ⊕ V2 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)

lemma mulVec_leftIndicator (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (i : V1 ⊕ V2) :
    (X *ᵥ leftIndicator) i = leftSum X i := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, leftIndicator]

lemma mulVec_rightIndicator (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (i : V1 ⊕ V2) :
    (X *ᵥ rightIndicator) i = rightSum X i := by
  simp [mulVec, dotProduct, Fintype.sum_sum_type, rightIndicator]

lemma liftValue_leftIndicator (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    liftValue X leftIndicator = ∑ i : V1, leftSum X (Sum.inl i) := by
  simp [liftValue, dotProduct, Fintype.sum_sum_type, leftIndicator, mulVec,
    Finset.sum_add_distrib]

lemma liftValue_rightIndicator (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    liftValue X rightIndicator = ∑ j : V2, rightSum X (Sum.inr j) := by
  simp [liftValue, dotProduct, Fintype.sum_sum_type, rightIndicator, mulVec,
    Finset.sum_add_distrib]

lemma liftMass_eq (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    liftMass X = liftValue X leftIndicator + liftValue X rightIndicator := by
  simp [liftMass, liftValue_leftIndicator, liftValue_rightIndicator]

lemma liftMatrix_eq (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    liftMatrix X = genericLiftMatrix X leftIndicator + genericLiftMatrix X rightIndicator := by
  ext i j
  simp only [liftMatrix, genericLiftMatrix, Matrix.add_apply, liftWeight,
    mulVec_leftIndicator, mulVec_rightIndicator, leftScale, rightScale]
  ring

lemma liftMass_pos_of_objective_pos (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : X.PosSemidef) (hp : 0 < frob Cmat X) : 0 < liftMass X := by
  have hL := liftValue_nonneg hX (leftIndicator (V1 := V1) (V2 := V2))
  have hR := liftValue_nonneg hX (rightIndicator (V1 := V1) (V2 := V2))
  rw [liftMass_eq]
  by_contra hh
  have hzero : liftValue X leftIndicator = 0 := by linarith
  have hz := mulVec_eq_zero_of_liftValue_eq_zero hX leftIndicator hzero
  have hsym : X.IsSymm := (Matrix.isHermitian_iff_isSymm).mp hX.isHermitian
  have hobj : frob Cmat X = 0 := by
    rw [frob_Cmat_eq_cross X hsym, Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have hj := congrFun hz (Sum.inr j)
    rw [mulVec_leftIndicator] at hj
    simp only [Pi.zero_apply, leftSum] at hj
    convert hj using 1
    apply Finset.sum_congr rfl
    intro i _
    exact (hsym.apply _ _).symm
  linarith

lemma liftMatrix_normalized_bordered_psd (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : X.PosSemidef) (ht : 0 < liftMass X) :
    (bordered ((liftMass X)⁻¹ • liftMatrix X)).PosSemidef := by
  rw [liftMatrix_eq, liftMass_eq]
  apply bordered_sum_lift_posSemidef hX
  rwa [← liftMass_eq]

lemma frob_smul (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (c : ℝ) :
    frob Cmat (c • X) = c * frob Cmat X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma normalized_lift_feasible (E : V1 → V2 → Prop)
    (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X)
    (hp : 0 < frob Cmat X) :
    G1Feasible E ((liftMass X)⁻¹ • liftMatrix X) := by
  refine ⟨liftMatrix_normalized_bordered_psd X hX.1 (liftMass_pos_of_objective_pos X hX.1 hp), ?_⟩
  intro i j hij
  simp [Matrix.smul_apply, liftMatrix_vanishes E X hX.2.2 i j hij]

lemma normalized_lift_objective (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    (hX : X.PosSemidef) (hp : 0 < frob Cmat X) (h : ℝ)
    (hleft : ∀ i : V1, rightSum X (Sum.inl i) = 2 * h * X (Sum.inl i) (Sum.inl i))
    (hright : ∀ j : V2, leftSum X (Sum.inr j) = 2 * h * X (Sum.inr j) (Sum.inr j)) :
    frob Cmat ((liftMass X)⁻¹ • liftMatrix X) = 4 * h ^ 2 := by
  have hsym : X.IsSymm := Matrix.isHermitian_iff_isSymm.mp hX.isHermitian
  have hzero : ∀ i, X i i = 0 → ∀ j, X i j = 0 := by
    intro i hi j
    exact entry_eq_zero_of_diag_eq_zero hX hi j
  rw [frob_smul, liftMatrix_objective X hsym hzero h hleft hright]
  field_simp [ne_of_gt (liftMass_pos_of_objective_pos X hX hp)]

end
end BicliqueSDP.Chain.R6


set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace BicliqueSDP.Chain.H1Attainment

noncomputable section

lemma psd_entry_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) (i j : ι) :
    -1 ≤ X i j ∧ X i j ≤ 1 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have hdiag (k : ι) : X k k ≤ 1 := by
    calc
      X k k ≤ ∑ l, X l l :=
        Finset.single_le_sum (f := fun l => X l l)
          (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
      _ = 1 := htr
  have hsub := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  have hadd := hX.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at hsub
  simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single, single_dotProduct] at hadd
  constructor <;> linarith [hdiag i, hdiag j]

lemma isClosed_posSemidef {ι : Type*} [Fintype ι] :
    IsClosed {X : Matrix ι ι ℝ | X.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec,
    Matrix.IsHermitian, Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_eq (by fun_prop) continuous_id).inter ?_
  apply isClosed_iInter
  intro x
  exact isClosed_le continuous_const (by fun_prop)

variable {V1 V2 : Type} [Fintype V1] [Fintype V2]
  [DecidableEq V1] [DecidableEq V2]

omit [DecidableEq V1] [DecidableEq V2] in
lemma isClosed_h1Feasible (E : V1 → V2 → Prop) :
    IsClosed {X | H1Feasible E X} := by
  have hedge : IsClosed {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ |
      VanishesOnEdges E X} := by
    simp only [VanishesOnEdges, Set.ofPred_forall]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro _
    exact isClosed_eq (by fun_prop) continuous_const
  exact isClosed_posSemidef.inter
    ((isClosed_eq (by fun_prop) continuous_const).inter hedge)

lemma isCompact_h1Feasible (E : V1 → V2 → Prop) :
    IsCompact {X | H1Feasible E X} := by
  apply (isCompact_Icc : IsCompact
    (Set.Icc (fun (_ _ : V1 ⊕ V2) => (-1 : ℝ)) (fun _ _ => (1 : ℝ)))).of_isClosed_subset
      (isClosed_h1Feasible E)
  intro X hX
  constructor
  · intro i j
    exact (psd_entry_bounds hX.1 hX.2.1 i j).1
  · intro i j
    exact (psd_entry_bounds hX.1 hX.2.1 i j).2

omit [DecidableEq V1] [DecidableEq V2] in
lemma continuous_frob (M : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    Continuous (fun X => frob M X) := by
  unfold frob
  fun_prop

lemma h1_attained_of_pos (E : V1 → V2 → Prop) (hpos : 0 < h1 E) :
    ∃ X, H1Feasible E X ∧ frob Cmat X = h1 E := by
  have hnonempty : Set.Nonempty {X | H1Feasible E X} := by
    by_contra hempty
    have he : {X | H1Feasible E X} = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    simp [h1, he] at hpos
  obtain ⟨X, hX, hmax⟩ := (isCompact_h1Feasible E).exists_isMaxOn hnonempty
    (continuous_frob Cmat).continuousOn
  refine ⟨X, hX, ?_⟩
  have hb : BddAbove ((fun X => frob Cmat X) '' {X | H1Feasible E X}) := by
    refine ⟨frob Cmat X, ?_⟩
    rintro z ⟨Y, hY, rfl⟩
    exact hmax hY
  apply le_antisymm
  · exact le_csSup hb ⟨X, hX, rfl⟩
  · change sSup ((fun X => frob Cmat X) '' {X | H1Feasible E X}) ≤ frob Cmat X
    apply csSup_le (hnonempty.image (fun X => frob Cmat X))
    rintro z ⟨Y, hY, rfl⟩
    exact hmax hY

end

end BicliqueSDP.Chain.H1Attainment

namespace BicliqueSDP.Chain.R6.G1Bounds
open Matrix
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
lemma psd_of_bordered {X : Matrix ι ι ℝ} (hX : (bordered X).PosSemidef) :
    X.PosSemidef := by
  exact hX.submatrix (Sum.inr : ι → Unit ⊕ ι)

lemma diag_le_one_of_bordered {X : Matrix ι ι ℝ} (hX : (bordered X).PosSemidef)
    (i : ι) : X i i ≤ 1 := by
  have hd := hX.dotProduct_mulVec_nonneg
    (Pi.single (Sum.inl ()) (-X i i) + Pi.single (Sum.inr i) 1)
  simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single, single_dotProduct, bordered, Matrix.fromBlocks] at hd
  nlinarith

lemma psd_entry_le_diag_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (i j : ι) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
lemma g1_objective_bddAbove (E : V1 → V2 → Prop) :
    BddAbove ((fun X => frob Cmat X) '' {X | G1Feasible E X}) := by
  refine ⟨∑ _ : V1 ⊕ V2, ∑ _ : V1 ⊕ V2, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  have hx := psd_entry_le_diag_avg (psd_of_bordered hX.1) u v
  have hu := diag_le_one_of_bordered hX.1 u
  have hv := diag_le_one_of_bordered hX.1 v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

end BicliqueSDP.Chain.R6.G1Bounds


open Matrix
open scoped BigOperators

namespace BicliqueSDP.Chain.RelationsProof

noncomputable section

lemma psd_entry_le_diag_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (i j : ι) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

lemma psd_entry_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) (i j : ι) :
    X i j ≤ 1 := by
  have hdiag (k : ι) : X k k ≤ 1 := by
    calc X k k ≤ ∑ l, X l l := Finset.single_le_sum (f := fun l => X l l) (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
         _ = 1 := htr
  have hpair := psd_entry_le_diag_avg hX i j
  linarith [hdiag i, hdiag j]

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

lemma h1_objective_bddAbove (E : V1 → V2 → Prop) :
    BddAbove ((fun X => frob Cmat X) '' {X | H1Feasible E X}) := by
  refine ⟨∑ _ : V1 ⊕ V2, ∑ _ : V1 ⊕ V2, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  have hx := psd_entry_le_one hX.1 hX.2.1 u v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

lemma frob_smul_right {ι : Type} [Fintype ι] (a : ℝ) (M X : Matrix ι ι ℝ) :
    frob M (a • X) = a * frob M X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

lemma psd_objective_le_trace_mul_h1 (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hp : X.PosSemidef)
    (hE : VanishesOnEdges E X) :
    frob Cmat X ≤ X.trace * h1 E := by
  obtain ht | ht := eq_or_lt_of_le hp.trace_nonneg
  · have hz : X = 0 := hp.trace_eq_zero_iff.mp ht.symm
    simp [hz, frob]
  · have hnorm : H1Feasible E (X.trace⁻¹ • X) := by
      refine ⟨hp.smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
      · simp [Matrix.trace_smul, ht.ne']
      · intro u v huv
        simp [hE u v huv]
    have hle := le_csSup (h1_objective_bddAbove E) ⟨X.trace⁻¹ • X, hnorm, rfl⟩
    change frob Cmat (X.trace⁻¹ • X) ≤ h1 E at hle
    rw [frob_smul_right] at hle
    have := (div_le_iff₀ ht).mp (show frob Cmat X / X.trace ≤ h1 E by
      simpa [div_eq_mul_inv, mul_comm] using hle)
    simpa [mul_comm] using this

section Perturbation
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def coordScale (k : ι) (t : ℝ) (i : ι) : ℝ := if i = k then 1 + t else 1

def perturb (X : Matrix ι ι ℝ) (k : ι) (t : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (coordScale k t) * X * Matrix.diagonal (coordScale k t)

lemma perturb_apply (X : Matrix ι ι ℝ) (k : ι) (t : ℝ) (i j : ι) :
    perturb X k t i j = coordScale k t i * X i j * coordScale k t j := by
  simp [perturb, Matrix.diagonal_mul, Matrix.mul_diagonal]

lemma perturb_psd {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (k : ι) (t : ℝ) :
    (perturb X k t).PosSemidef := by
  simpa [perturb] using hX.mul_mul_conjTranspose_same (Matrix.diagonal (coordScale k t))

lemma perturb_trace (X : Matrix ι ι ℝ) (k : ι) (t : ℝ) :
    (perturb X k t).trace = X.trace + (2 * t + t ^ 2) * X k k := by
  have he (i : ι) : perturb X k t i i =
      X i i + if i = k then (2 * t + t ^ 2) * X k k else 0 := by
    by_cases hi : i = k
    · subst i
      simp [perturb_apply, coordScale]
      ring
    · simp [perturb_apply, coordScale, hi]
  simp only [Matrix.trace, Matrix.diag, he, Finset.sum_add_distrib]
  simp

lemma perturb_frob (C X : Matrix ι ι ℝ) (k : ι) (t : ℝ)
    (hC : C.IsSymm) (hX : X.IsSymm) (hdiag : C k k = 0) :
    frob C (perturb X k t) = frob C X + 2 * t * (∑ j, C k j * X k j) := by
  have he (i j : ι) : C i j * perturb X k t i j = C i j * X i j +
      (if i = k then t * (C i j * X i j) else 0) +
      (if j = k then t * (C i j * X i j) else 0) := by
    by_cases hi : i = k <;> by_cases hj : j = k
    · subst i; subst j
      simp [hdiag]
    · simp [perturb_apply, coordScale, hi, hj]
      ring
    · simp [perturb_apply, coordScale, hi, hj]
      ring
    · simp [perturb_apply, coordScale, hi, hj]
  simp only [frob, he, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  have hs : (∑ i, t * (C i k * X i k)) = ∑ i, t * (C k i * X k i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← hC.apply i k, ← hX.apply i k]
  rw [hs]
  rw [← Finset.mul_sum]
  ring

end Perturbation

lemma optimal_weighted_row (E : V1 → V2 → Prop)
    (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X)
    (hopt : frob Cmat X = h1 E) (k : V1 ⊕ V2) :
    (∑ j, Cmat k j * X k j) = h1 E * X k k := by
  have hC : (Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ).IsSymm := by
    ext i j
    cases i <;> cases j <;> simp [Cmat, Matrix.fromBlocks, Matrix.transpose_apply]
  have hS : X.IsSymm := Matrix.isHermitian_iff_isSymm.mp hX.1.isHermitian
  have hdiag : (Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) k k = 0 := by
    cases k <;> simp [Cmat, Matrix.fromBlocks]
  have hq (t : ℝ) : 0 ≤ (h1 E * X k k) * (t * t) +
      (2 * h1 E * X k k - 2 * ∑ j, Cmat k j * X k j) * t + 0 := by
    have hE : VanishesOnEdges E (perturb X k t) := by
      intro u v huv
      simp [perturb_apply, hX.2.2 u v huv]
    have hle := psd_objective_le_trace_mul_h1 E (perturb_psd hX.1 k t) hE
    rw [perturb_trace, perturb_frob Cmat X k t hC hS hdiag, hX.2.1, hopt] at hle
    nlinarith
  have hd := discrim_le_zero hq
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg (2 * h1 E * X k k - 2 * ∑ j, Cmat k j * X k j)]

end
end BicliqueSDP.Chain.RelationsProof


open BicliqueSDP.Chain BicliqueSDP.Chain.RelationsProof in
/-- Relations (40) and (41) follow from coordinate scaling at an optimal primal matrix. -/
theorem BicliqueSDP.Chain.R6.relations_direct {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) (hX : H1Feasible E X)
    (hopt : frob Cmat X = h1 E) :
    (∀ i : V1, ∑ j : V2, X (Sum.inl i) (Sum.inr j) = 2 * h1 E * X (Sum.inl i) (Sum.inl i)) ∧
    (∀ j : V2, ∑ i : V1, X (Sum.inr j) (Sum.inl i) = 2 * h1 E * X (Sum.inr j) (Sum.inr j)) := by
  constructor
  · intro i
    have hi := optimal_weighted_row E X hX hopt (Sum.inl i)
    simp [Cmat, Matrix.fromBlocks, ← Finset.mul_sum] at hi
    linarith
  · intro j
    have hj := optimal_weighted_row E X hX hopt (Sum.inr j)
    simp [Cmat, Matrix.fromBlocks, ← Finset.mul_sum] at hj
    linarith


open BicliqueSDP.Chain

/-- A normalized sum of two diagonal-congruence lifts converts an optimum of the
trace-one SDP into a bordered SDP point of objective `4 * (h1 E)^2`. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) : h1 E ≤ (1 / 2) * Real.sqrt (g1 E) := by
  classical
  by_cases hp : 0 < h1 E
  · obtain ⟨X, hX, hopt⟩ := H1Attainment.h1_attained_of_pos E hp
    have hpX : 0 < frob Cmat X := by rwa [hopt]
    obtain ⟨hleft, hright⟩ := R6.relations_direct E X hX hopt
    have hfeas := R6.normalized_lift_feasible E X hX hpX
    have hvalue := R6.normalized_lift_objective X hX.1 hpX (h1 E) hleft hright
    have hle := le_csSup (R6.G1Bounds.g1_objective_bddAbove E)
      ⟨(R6.liftMass X)⁻¹ • R6.liftMatrix X, hfeas, rfl⟩
    change frob Cmat ((R6.liftMass X)⁻¹ • R6.liftMatrix X) ≤ g1 E at hle
    rw [hvalue] at hle
    have hg : 0 ≤ g1 E := (by positivity : 0 ≤ 4 * h1 E ^ 2).trans hle
    nlinarith [Real.sq_sqrt hg, Real.sqrt_nonneg (g1 E)]
  · exact (le_of_not_gt hp).trans
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
