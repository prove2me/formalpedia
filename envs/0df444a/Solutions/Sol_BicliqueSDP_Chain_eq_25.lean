-- Prove2me | solution 1 for BicliqueSDP.Chain.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:43:29.842236+00:00
-- url     : https://prove2.me/submissions/4dbf7b68-867e-479e-8ba8-83c68fdb7882

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

open Matrix
open scoped BigOperators

namespace BicliqueSDP.Chain.Eq25Proof

noncomputable section

section Bounds
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

lemma trace_le_card_of_bordered {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) : X.trace ≤ Fintype.card ι := by
  calc
    X.trace = ∑ i, X i i := rfl
    _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => diag_le_one_of_bordered hX i)
    _ = Fintype.card ι := by simp

omit [Fintype ι] in
lemma bordered_zero_psd : (bordered (0 : Matrix ι ι ℝ)).PosSemidef := by
  have hd : (Matrix.diagonal (fun u : Unit ⊕ ι =>
      match u with | .inl _ => (1 : ℝ) | .inr _ => 0)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro u
    cases u <;> simp
  convert hd using 1
  ext u v
  cases u <;> cases v <;> simp [bordered, Matrix.diagonal, Matrix.fromBlocks]

lemma las1_values_bddAbove (G : SimpleGraph ι) :
    BddAbove ((fun X : Matrix ι ι ℝ => X.trace) ''
      {X | (bordered X).PosSemidef ∧ ∀ i j, G.Adj i j → X i j = 0}) := by
  refine ⟨Fintype.card ι, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact trace_le_card_of_bordered hX.1

lemma trace_le_las1 {G : SimpleGraph ι} {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) (hE : ∀ i j, G.Adj i j → X i j = 0) :
    X.trace ≤ las1 G := by
  exact le_csSup (las1_values_bddAbove G) ⟨X, ⟨hX, hE⟩, rfl⟩

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

lemma theta_objective_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove ((fun X : Matrix V V ℝ => ∑ i, ∑ j, X i j) ''
      {X | X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0}) := by
  classical
  refine ⟨∑ _ : V, ∑ _ : V, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => psd_entry_le_one hX.1 hX.2.1 i j

lemma sum_le_theta {V : Type} [Fintype V] (G : SimpleGraph V)
    (X : Matrix V V ℝ)
    (hX : X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0) :
    (∑ i, ∑ j, X i j) ≤ theta G := by
  exact le_csSup (theta_objective_bddAbove G) ⟨X, hX, rfl⟩

lemma theta_nonneg {V : Type} [Fintype V] (G : SimpleGraph V) : 0 ≤ theta G := by
  by_cases hn : {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1 ∧
      ∀ i j, G.Adj i j → X i j = 0}.Nonempty
  · obtain ⟨X, hX⟩ := hn
    have hz : 0 ≤ ∑ i, ∑ j, X i j := by
      simpa [dotProduct, Matrix.mulVec] using
        hX.1.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
    exact hz.trans (sum_le_theta G X hX)
  · simp [theta, Set.not_nonempty_iff_eq_empty.mp hn]

omit [DecidableEq ι] in
lemma trace_sq_le_sum_of_bordered {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) : X.trace ^ 2 ≤ ∑ i, ∑ j, X i j := by
  have h := hX.dotProduct_mulVec_nonneg
    (Sum.elim (fun _ : Unit => -X.trace) (fun _ : ι => (1 : ℝ)))
  simp [dotProduct, Matrix.mulVec, bordered, Matrix.fromBlocks,
    Fintype.sum_sum_type, Finset.mul_sum,
    Matrix.trace, Matrix.diag] at h ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul] at h
  nlinarith

omit [DecidableEq ι] in
lemma trace_le_theta {G : SimpleGraph ι} {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) (hE : ∀ i j, G.Adj i j → X i j = 0) :
    X.trace ≤ theta G := by
  have hp := psd_of_bordered hX
  obtain ht | ht := eq_or_lt_of_le hp.trace_nonneg
  · rw [← ht]
    exact theta_nonneg G
  · have hnorm : (X.trace⁻¹ • X).PosSemidef ∧ (X.trace⁻¹ • X).trace = 1 ∧
        ∀ i j, G.Adj i j → (X.trace⁻¹ • X) i j = 0 := by
      refine ⟨hp.smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
      · simp [Matrix.trace_smul, ht.ne']
      · intro i j hij
        simp [hE i j hij]
    have hle := sum_le_theta G (X.trace⁻¹ • X) hnorm
    have hdiv : (∑ i, ∑ j, X i j) / X.trace ≤ theta G := by
      simpa [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_comm] using hle
    have hs := (div_le_iff₀ ht).mp hdiv
    have hsq := trace_sq_le_sum_of_bordered hX
    nlinarith

lemma las1_le_theta (G : SimpleGraph ι) : las1 G ≤ theta G := by
  apply csSup_le
  · refine ⟨0, 0, ⟨bordered_zero_psd, ?_⟩, by simp⟩
    intro i j _
    rfl
  · rintro z ⟨X, hX, rfl⟩
    exact trace_le_theta hX.1 hX.2

end Bounds

section Lift
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

end Lift

section Converse
variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma bordered_lift_posSemidef {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (u : ι → ℝ)
    (ht : 0 < liftValue X u) :
    (bordered ((liftValue X u)⁻¹ • genericLiftMatrix X u)).PosSemidef := by
  have heq : bordered ((liftValue X u)⁻¹ • genericLiftMatrix X u) =
      (liftValue X u)⁻¹ • rawLift X u := by
    ext (i | i) (j | j) <;>
      simp [bordered, rawLift, Matrix.fromBlocks, ne_of_gt ht]
  rw [heq]
  exact (rawLift_posSemidef hX u).smul (inv_nonneg.mpr ht.le)

lemma lift_ones_trace_bound {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (htr : X.trace = 1) :
    (liftValue X (fun _ => 1)) ^ 2 ≤ (genericLiftMatrix X (fun _ => 1)).trace := by
  let s := liftValue X (fun _ => 1)
  have hn : 0 ≤ ∑ i, (liftWeight X (fun _ => 1) i - s) ^ 2 * X i i := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) hX.diag_nonneg
  have he (i : ι) : (liftWeight X (fun _ => 1) i - s) ^ 2 * X i i =
      genericLiftMatrix X (fun _ => 1) i i - 2 * s * (X *ᵥ (fun _ => 1)) i +
        s ^ 2 * X i i := by
    rw [← liftWeight_mul_diag hX (fun _ => 1) i]
    dsimp [genericLiftMatrix]
    ring
  simp_rw [he] at hn
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hn
  have hb : (∑ i, (X *ᵥ (fun _ => 1)) i) = s := by simp [s, liftValue, dotProduct]
  rw [hb] at hn
  change 0 ≤ (genericLiftMatrix X (fun _ => 1)).trace - 2 * s * s + s ^ 2 * X.trace at hn
  rw [htr] at hn
  change s ^ 2 ≤ _
  nlinarith

lemma las1_nonneg (G : SimpleGraph ι) : 0 ≤ las1 G := by
  have hz : (0 : Matrix ι ι ℝ).trace ≤ las1 G :=
    trace_le_las1 bordered_zero_psd (fun _ _ _ => rfl)
  simpa using hz

lemma theta_objective_le_las1 (G : SimpleGraph ι) (X : Matrix ι ι ℝ)
    (hX : X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0) :
    (∑ i, ∑ j, X i j) ≤ las1 G := by
  let s := liftValue X (fun _ => 1)
  have hs : s = ∑ i, ∑ j, X i j := by simp [s, liftValue, dotProduct, Matrix.mulVec]
  rw [← hs]
  by_cases hp : 0 < s
  · let Y := s⁻¹ • genericLiftMatrix X (fun _ => 1)
    have hY : (bordered Y).PosSemidef := bordered_lift_posSemidef hX.1 _ hp
    have he : ∀ i j, G.Adj i j → Y i j = 0 := by
      intro i j hij
      simp [Y, genericLiftMatrix, hX.2.2 i j hij]
    have hl := trace_le_las1 hY he
    have hb := lift_ones_trace_bound hX.1 hX.2.1
    have hlow : s ≤ Y.trace := by
      change s ≤ (s⁻¹ • genericLiftMatrix X (fun _ => 1)).trace
      rw [Matrix.trace_smul]
      change s ≤ s⁻¹ * (genericLiftMatrix X (fun _ => 1)).trace
      rw [mul_comm, ← div_eq_mul_inv]
      apply (le_div_iff₀ hp).mpr
      change s * s ≤ (genericLiftMatrix X (fun _ => 1)).trace
      simpa [s, pow_two] using hb
    exact hlow.trans hl
  · exact (le_of_not_gt hp).trans (las1_nonneg G)

lemma theta_le_las1 (G : SimpleGraph ι) : theta G ≤ las1 G := by
  by_cases hn : {X : Matrix ι ι ℝ | X.PosSemidef ∧ X.trace = 1 ∧
      ∀ i j, G.Adj i j → X i j = 0}.Nonempty
  · apply csSup_le
    · exact hn.image _
    · rintro z ⟨X, hX, rfl⟩
      exact theta_objective_le_las1 G X hX
  · simp [theta, Set.not_nonempty_iff_eq_empty.mp hn, las1_nonneg G]

end Converse
end
end BicliqueSDP.Chain.Eq25Proof

open BicliqueSDP.Chain BicliqueSDP.Chain.Eq25Proof in
/-- The two primal formulations of the Lovász theta number agree. -/
theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) : las1 G = theta G := by
  classical
  exact le_antisymm (las1_le_theta G) (theta_le_las1 G)
