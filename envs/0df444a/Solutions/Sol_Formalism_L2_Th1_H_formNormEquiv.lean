-- Prove2me | solution 1 for Formalism.L2.Th1.H.formNormEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:20.866478+00:00
-- url     : https://prove2.me/submissions/3e479b94-def6-4c33-96d2-5e70b3b5cdfd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : FormNorm := by
  intro V _ _ _ H hH hpos
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hhom : ∀ (r : ℝ) (z : V), (H ((r : ℂ) • z) ((r : ℂ) • z)).re = r ^ 2 * (H z z).re := by
    intro r z
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring
  let b := Module.finBasis ℂ V
  have hexp : ∀ z, H z z = ∑ i, ∑ j, conj (b.repr z i) * (b.repr z j * H (b j) (b i)) := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
  have hcont : Continuous fun z : V => (H z z).re := by
    have hc : ∀ i, Continuous fun z : V => b.repr z i := fun i => (b.coord i).continuous_of_finiteDimensional
    have e : (fun z : V => (H z z).re)
        = fun z => (∑ i, ∑ j, conj (b.repr z i) * (b.repr z j * H (b j) (b i))).re := by
      funext z; rw [hexp z]
    rw [e]
    exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (Complex.continuous_conj.comp (hc i)).mul ((hc j).mul continuous_const))
  have hunit : ∀ w : V, w ≠ 0 → ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ Metric.sphere (0 : V) 1 := fun w hw => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]
  by_cases hV : ∃ v : V, v ≠ 0
  swap
  · push_neg at hV
    refine ⟨1, 1, one_pos, one_pos, fun z => ?_⟩
    rw [hV z]; simp
  obtain ⟨v, hv⟩ := hV
  have hsph : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : V) 1).Nonempty := ⟨_, hunit v hv⟩
  obtain ⟨a, ha, hamin⟩ := hsph.exists_isMinOn hne hcont.continuousOn
  obtain ⟨m, hm, hmmax⟩ := hsph.exists_isMaxOn hne hcont.continuousOn
  have ha0 : a ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at ha; exact zero_ne_one ha
  have hcpos : 0 < (H a a).re := hpos a ha0
  refine ⟨(H a a).re, (H m m).re, hcpos, lt_of_lt_of_le hcpos (isMaxOn_iff.1 hmmax a ha), fun z => ?_⟩
  by_cases hz : z = 0
  · subst hz; simp
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := isMinOn_iff.1 hamin _ (hunit z hz)
  have h2 := isMaxOn_iff.1 hmmax _ (hunit z hz)
  rw [hhom] at h1 h2
  have e : (‖z‖⁻¹) ^ 2 * (H z z).re * ‖z‖ ^ 2 = (H z z).re := by field_simp
  have hr2 : 0 ≤ ‖z‖ ^ 2 := by positivity
  constructor
  · calc (H a a).re * ‖z‖ ^ 2 ≤ (‖z‖⁻¹) ^ 2 * (H z z).re * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right h1 hr2
      _ = (H z z).re := e
  · calc (H z z).re = (‖z‖⁻¹) ^ 2 * (H z z).re * ‖z‖ ^ 2 := e.symm
      _ ≤ (H m m).re * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right h2 hr2
end Formalism.L2.Th1.H
