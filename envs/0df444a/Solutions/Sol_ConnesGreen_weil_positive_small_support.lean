-- Prove2me | solution 1 for ConnesGreen.weil_positive_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T04:28:46.960075+00:00
-- url     : https://prove2.me/submissions/39504f21-6305-4ac9-b4d9-b38d1bcdf5b5

import Theorems.Thm_ConnesGreen_smallSupportCost_positive
import Theorems.Thm_ConnesGreen_arch_convolution_re_ge_frequency_mass
import Theorems.Thm_ConnesGreen_pole_pair_mass_bound
import Theorems.Thm_ConnesGreen_prime_convolution_zero_small_support
import Theorems.Thm_ConnesGreen_gammaBracket_positive_cutoff
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace ConnesGreen
theorem positiveGammaCutoff_positive : 0 < positiveGammaCutoff := by
  unfold positiveGammaCutoff
  positivity

theorem _root_.solution (T : ℝ) (hT : 0 ≤ T)
    (hTr : T ≤ positiveSupportRadius) (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (1 / 2 : ℝ) * (∫ s : ℝ, ‖g s‖ ^ 2) ≤
      (weilDistribution (conv g (starInv g))).re := by
  have hrad := hTr
  unfold positiveSupportRadius at hrad
  have hprime : 2 * T ≤ Real.log 2 := by linarith [hrad.trans (min_le_left _ _)]
  have hT1 : T ≤ 1 := hrad.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcp := smallSupportCost_positive
  have hcost : smallSupportCost * T ≤ 1 / 2 := by
    have hr := hrad.trans ((min_le_right _ _).trans (min_le_right _ _))
    have he := (le_div_iff₀ (by positivity : 0 < 2 * smallSupportCost)).mp hr
    nlinarith
  have ha : (Zeta23.EF.gammaBracket positiveGammaCutoff - (Zeta23.EF.gammaBracket positiveGammaCutoff - Zeta23.EF.gammaBracket 0) * (2 * positiveGammaCutoff * T / Real.pi)) * (∫ s : ℝ, ‖g s‖ ^ 2) ≤ (archTerm (conv g (starInv g))).re := by
    simpa [Zeta23.EF.gammaBracket] using arch_convolution_re_ge_frequency_mass positiveGammaCutoff T positiveGammaCutoff_positive.le hT g hg
  have hp := pole_pair_mass_bound T hT g hg
  have hL : 0 ≤ ∫ s : ℝ, ‖g s‖ ^ 2 := integral_nonneg (fun s => sq_nonneg _)
  have hexp : Real.exp T ≤ Real.exp 1 := Real.exp_le_exp.mpr hT1
  have hp' := hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4 * T)) hL)
  have hre := Complex.abs_re_le_norm
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1)
  have hneg := neg_abs_le
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re
  have he : (weilDistribution (conv g (starInv g))).re =
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re +
        (archTerm (conv g (starInv g))).re := by
    unfold weilDistribution
    rw [prime_convolution_zero_small_support T g hg hprime]
    simp
  have hcoef : 1 / 2 ≤ Zeta23.EF.gammaBracket positiveGammaCutoff -
      (Zeta23.EF.gammaBracket positiveGammaCutoff - Zeta23.EF.gammaBracket 0) *
        (2 * positiveGammaCutoff * T / Real.pi) - 4 * T * Real.exp 1 := by
    have hγ : 1 ≤ Zeta23.EF.gammaBracket positiveGammaCutoff := by
      simpa [Zeta23.EF.gammaBracket, positiveGammaCutoff] using gammaBracket_positive_cutoff
    unfold smallSupportCost at hcost
    have heq :
        (Zeta23.EF.gammaBracket positiveGammaCutoff - Zeta23.EF.gammaBracket 0) *
          (2 * positiveGammaCutoff * T / Real.pi) + 4 * T * Real.exp 1 =
        ((Zeta23.EF.gammaBracket positiveGammaCutoff - Zeta23.EF.gammaBracket 0) *
          (2 * positiveGammaCutoff / Real.pi) + 4 * Real.exp 1) * T := by ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hcoef hL
  rw [he]
  nlinarith
end ConnesGreen
