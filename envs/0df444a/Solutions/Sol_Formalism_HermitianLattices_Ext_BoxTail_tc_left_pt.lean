-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_left_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:16.661021+00:00
-- url     : https://prove2.me/submissions/b28bee18-fcca-4a0d-9f4c-de5ce3850d0b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z η σ M : ℝ) (hz : 0 < z)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hσ0 : 0 < σ) (hσ1 : σ < 1) (u : ℝ)
    (hM : ‖Formalism.ZeroFreeDirichlet.negLD χ ((σ : ℂ) + (u : ℂ) * I)‖ ≤ M) :
    ‖Formalism.ZeroFreeDirichlet.Fchi χ (z + z * η) ((σ : ℂ) + (u : ℂ) * I) - Formalism.ZeroFreeDirichlet.Fchi χ z ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      M * (4 * η * z ^ σ) * (1 / ‖(σ : ℂ) + (u : ℂ) * I - 1‖) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    rw [hre] at h1
    simp at h1
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp [hre] at h1
    linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hdiff : ‖((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s‖ ≤
      ‖s‖ * z ^ (σ - 1) * (z + z * η - z) := by
    have hab : z ≤ z + z * η := by nlinarith
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun w : ℝ => ((w : ℂ)) ^ s)
      (f' := fun w : ℝ => s * ((w : ℂ)) ^ (s - 1)) ?_ ?_ (z + z * η) ⟨hab, le_rfl⟩
    · intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le hz hw.1
      have h := (hasStrictDerivAt_cpow_const (c := s) (Complex.ofReal_mem_slitPlane.2 hw0)).hasDerivAt
      exact h.comp_ofReal.hasDerivWithinAt
    · intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le hz hw.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw0]
      have hre1 : (s - 1).re = σ - 1 := by simp [hre]
      rw [hre1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz hw.1 (by linarith))
        (norm_nonneg _)
  have hz1 : z ^ (σ - 1) * (z + z * η - z) = η * z ^ σ := by
    rw [Real.rpow_sub_one hz.ne']
    field_simp
    ring
  have h2 : ‖((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s‖ ≤ ‖s‖ * (η * z ^ σ) := by
    rw [← hz1, ← mul_assoc]
    exact hdiff
  unfold Formalism.ZeroFreeDirichlet.Fchi
  have e : Formalism.ZeroFreeDirichlet.negLD χ s * ((z + z * η : ℝ) : ℂ) ^ s / (s * (s - 1)) -
      Formalism.ZeroFreeDirichlet.negLD χ s * ((z : ℝ) : ℂ) ^ s / (s * (s - 1)) =
      Formalism.ZeroFreeDirichlet.negLD χ s * (((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s) / (s * (s - 1)) := by
    ring
  rw [e, norm_div, norm_mul, norm_mul]
  have hsn : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hs1n : 0 < ‖s - 1‖ := norm_pos_iff.2 hs1
  rw [div_le_iff₀ (by positivity)]
  have key : M * (4 * η * z ^ σ) * (1 / ‖s - 1‖) * (‖s‖ * ‖s - 1‖) =
      4 * (M * (‖s‖ * (η * z ^ σ))) := by
    field_simp
  rw [key]
  have hP : 0 ≤ M * (‖s‖ * (η * z ^ σ)) := by positivity
  have h3 : ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ * ‖((z + z * η : ℝ) : ℂ) ^ s - ((z : ℝ) : ℂ) ^ s‖ ≤
      M * (‖s‖ * (η * z ^ σ)) := mul_le_mul hM h2 (norm_nonneg _) hM0
  linarith
end Formalism.HermitianLattices.Ext.BoxTail
