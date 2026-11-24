-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_coercive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:02.505895+00:00
-- url     : https://prove2.me/submissions/0f4269f0-41b7-4a1d-bcb7-920aff609496

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (G : Matrix ι ι ℚ)
    (hG : ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w)) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : ι → ℝ, l * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by
  set M : Matrix ι ι ℝ := (G + Gᵀ).map (Rat.cast : ℚ → ℝ) with hM
  have hcf : ∀ w : ι → ℚ, (fun i => (w i : ℝ)) ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) =
      2 * ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by
    intro w
    have h1 : ((G + Gᵀ).map (Rat.cast : ℚ → ℝ)) = G.map (Rat.cast : ℚ → ℝ) + (G.map (Rat.cast : ℚ → ℝ))ᵀ := by
      ext i j
      simp
    have h2 : ∀ M : Matrix ι ι ℝ, ∀ v : ι → ℝ, v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
      intro M v
      simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have h3 : (((w ⬝ᵥ (G *ᵥ w)) : ℚ) : ℝ) =
        (fun i => (w i : ℝ)) ⬝ᵥ (G.map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply]
      push_cast
      try rfl
    rw [h1, Matrix.add_mulVec, dotProduct_add, h2, ← h3]
    ring
  have hcont : Continuous fun v : ι → ℝ => v ⬝ᵥ (M *ᵥ v) := by
    first
    | fun_prop
    | exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hGnn : ∀ w : ι → ℚ, 0 ≤ w ⬝ᵥ (G *ᵥ w) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp
    · exact (hG w hw).le
  have hd := DenseRange.piMap (X := fun _ : ι => ℚ) (Y := fun _ : ι => ℝ)
    (fun _ => Rat.denseRange_cast)
  have hpsd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    refine hd.induction_on v (isClosed_le continuous_const hcont) (fun w => ?_)
    show 0 ≤ (fun i => (w i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (w i : ℝ))
    rw [hM, hcf]
    exact mul_nonneg zero_le_two (by exact_mod_cast hGnn w)
  have hPSD : M.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · unfold Matrix.IsHermitian
      ext i j
      simp [hM, add_comm]
    · rw [star_trivial]
      exact hpsd x
  have hdef : ∀ v : ι → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v) := by
    intro v hv
    rcases (hpsd v).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hSv : M *ᵥ v = 0 := by
        refine (hPSD.dotProduct_mulVec_zero_iff v).mp ?_
        rw [star_trivial]
        exact heq.symm
      have hdetS : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hSv⟩
      have hdet : (((G + Gᵀ).det : ℚ) : ℝ) = 0 := by
        rw [← hdetS]
        exact RingHom.map_det (Rat.castHom ℝ) (G + Gᵀ)
      have hdetQ : (G + Gᵀ).det = 0 := by exact_mod_cast hdet
      obtain ⟨w, hw, hGw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQ
      have h0 : w ⬝ᵥ ((G + Gᵀ) *ᵥ w) = 0 := by rw [hGw, dotProduct_zero]
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
        dotProduct_comm w (Matrix.vecMul w G), ← Matrix.dotProduct_mulVec] at h0
      have := hG w hw
      linarith
  by_cases hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ :=
      (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hu
      exact zero_ne_one hu
    refine ⟨u ⬝ᵥ (M *ᵥ u), hdef u hu0, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
      have hm := isMinOn_iff.mp hmin _ hmem
      simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hm
      have hc2 : ‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ (M *ᵥ v))) * ‖v‖ ^ 2 = v ⬝ᵥ (M *ᵥ v) := by
        field_simp
      calc u ⬝ᵥ (M *ᵥ u) * ‖v‖ ^ 2
          ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ (M *ᵥ v))) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hm (sq_nonneg _)
        _ = v ⬝ᵥ (M *ᵥ v) := hc2
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · exfalso
      apply hne
      have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
end Formalism.HermitianLatticesTheory
