-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.betaT_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:37.29648+00:00
-- url     : https://prove2.me/submissions/820626a8-444e-4efe-8f22-bc0562020003

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (m z o S e : ℕ) : betaT p m z o S e ≠ 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hA : e.factorial * (z + e).choose e ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'
  have hB : o.factorial * S.factorial ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  simp only [betaT]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hp0) (Nat.cast_ne_zero.mpr hA)) (Nat.cast_ne_zero.mpr hB)
end Formalism.GM.MeanGammaLemmas
