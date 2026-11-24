-- Prove2me | solution 1 for Formalism.L2.Th1.H.GaussIntegrable_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:04.550026+00:00
-- url     : https://prove2.me/submissions/f87729e7-528c-47fc-8eb2-ab3a869b6e6e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Theorems.Thm_Formalism_L2_Th1_H_continuous_diag
import Theorems.Thm_Formalism_L2_Th1_H_exp_neg_sq_le_japanese

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : FormNorm) : GaussIntegrable := by
  intro V _ _ _ _ _ μ _ H hH hP c hc
  obtain ⟨c₀, C, hc₀, _, hb⟩ := h V H hH hP
  have hcont : Continuous fun z => Real.exp (-c * (H z z).re) :=
    Real.continuous_exp.comp (continuous_const.mul (Complex.continuous_re.comp (continuous_diag H)))
  set m : ℕ := Module.finrank ℝ V + 1 with hm
  have hJ : Integrable (fun z : V => (1 + ‖z‖) ^ (-((2 * m : ℕ) : ℝ))) μ :=
    integrable_one_add_norm (by
      have : Module.finrank ℝ V < 2 * m := by omega
      exact_mod_cast this)
  have ha : 0 < c * c₀ := by positivity
  have hint : Integrable (fun z => Real.exp (-c * (H z z).re)) μ := by
    refine Integrable.mono' (hJ.const_mul (Real.exp (c * c₀) * (m ! : ℝ) * 2 ^ m / (c * c₀) ^ m))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_sq_le_japanese ha m (norm_nonneg z))
    have := (hb z).1
    nlinarith
  refine ⟨hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun z => Real.exp (-c * (H z z).re)) = Set.univ := by
    ext z
    simp [Real.exp_ne_zero]
  rw [hsupp]
  exact isOpen_univ.measure_pos μ Set.univ_nonempty
end Formalism.L2.Th1.H
