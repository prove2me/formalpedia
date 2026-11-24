-- Prove2me | solution 1 for Formalism.L2.Th1.F.PeriodAreaSignLemmas.altE_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:03:15.831473+00:00
-- url     : https://prove2.me/submissions/0c9ce3a3-cc87-423b-8ccd-815400a5e9c6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_eq
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_area_pos
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_det_eq_sgn_mul

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PeriodAreaSignLemmas
open Formalism.L2.Th1.F.PeriodAreaSignLemmas
namespace Formalism.L2.Th1.F.PeriodAreaSignLemmas
theorem _root_.solution (L : PeriodPair) (m n m' n' : ℤ) :
    altE L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)
      = ((-(sgn L * (m * n' - n * m')) : ℤ) : ℝ) := by
  have hA : area L ≠ 0 := (area_pos L).ne'
  rw [altE, herm, Complex.div_ofReal_im, div_eq_iff hA]
  have h1 : (((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) * conj ((m' : ℂ) * L.ω₁ + (n' : ℂ) * L.ω₂)).im
      = -((m * n' - n * m' : ℝ) * det L) := by
    rw [det_eq]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [h1, det_eq_sgn_mul]
  push_cast
  ring
end Formalism.L2.Th1.F.PeriodAreaSignLemmas
