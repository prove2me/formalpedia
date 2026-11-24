-- Prove2me | solution 1 for Formalism.L2.Th1.F.CmBy.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:23:36.530366+00:00
-- url     : https://prove2.me/submissions/22bc76eb-20fa-4a6d-9aa6-c1e881b86233

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
namespace Formalism.L2.Th1.F
namespace CmBy
private lemma re_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).re = (m : ℝ) + (n : ℝ) / 2 := by
  simp [omegaK]
  ring
private lemma im_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).im = (n : ℝ) * Real.sqrt d / 2 := by
  simp [omegaK]
  ring
end CmBy
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.CmBy
namespace Formalism.L2.Th1.F.CmBy
theorem _root_.solution (d : ℕ) (hd : 0 < d) (m n : ℤ) (h : (m, n) ≠ (0, 0)) :
    (m : ℂ) + (n : ℂ) * omegaK d ≠ 0 := by
  intro h0
  have hre := re_add_mul_omegaK d m n
  have him := im_add_mul_omegaK d m n
  rw [h0, Complex.zero_re] at hre
  rw [h0, Complex.zero_im] at him
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hn : (n : ℝ) = 0 := by
    have h2 : (n : ℝ) * Real.sqrt d = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · linarith
  have hm : (m : ℝ) = 0 := by rw [hn] at hre; linarith
  have hn' : n = 0 := by exact_mod_cast hn
  have hm' : m = 0 := by exact_mod_cast hm
  exact h (by rw [hm', hn'])
end Formalism.L2.Th1.F.CmBy
