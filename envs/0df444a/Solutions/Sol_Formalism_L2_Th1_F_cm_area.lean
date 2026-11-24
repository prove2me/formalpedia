-- Prove2me | solution 1 for Formalism.L2.Th1.F.cm_area
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:11.954827+00:00
-- url     : https://prove2.me/submissions/1bd38d31-ed27-4e21-8a05-7f1694fa24ee

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
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
namespace Formalism.L2.Th1.F
namespace Cm1
private theorem cmTheta_eq_half_b_add_sqrt_half_I (b : ℤ) (d : ℕ) :
    Formalism.L2.Th1.F.cmTheta b d = (((b : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  unfold Formalism.L2.Th1.F.cmTheta; push_cast; ring
private theorem im_ofReal_add_ofReal_mul_I (u v : ℝ) : ((u : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
end Cm1
open Cm1
private theorem area_cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    area (cmPair a b d ha hd) = (a : ℝ) * Real.sqrt d / 2 := by
  have key : conj (a : ℂ) * cmTheta b d
      = (((a : ℝ) * b / 2 : ℝ) : ℂ) + (((a : ℝ) * Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
    rw [map_natCast, _root_.Formalism.L2.Th1.F.Cm1.cmTheta_eq_half_b_add_sqrt_half_I]; push_cast; ring
  unfold area
  show |(conj (a : ℂ) * cmTheta b d).im| = _
  rw [key, _root_.Formalism.L2.Th1.F.Cm1.im_ofReal_add_ofReal_mul_I]
  exact abs_of_nonneg (by positivity)
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Cm1
namespace Formalism.L2.Th1.F
theorem _root_.solution : CmArea := by
  intro a b d ha hd
  exact area_cmPair a b d ha hd
end Formalism.L2.Th1.F
