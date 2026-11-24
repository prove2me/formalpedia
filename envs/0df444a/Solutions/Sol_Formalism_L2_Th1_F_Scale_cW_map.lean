-- Prove2me | solution 1 for Formalism.L2.Th1.F.Scale.cW_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:11.070976+00:00
-- url     : https://prove2.me/submissions/9a0b6055-6741-4964-abb2-230e3ff4a559

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSig1S
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Theorems.Thm_Formalism_L2_Th1_F_Scale_cW_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen uSer)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Scale
open PowerSeries
namespace Formalism.L2.Th1.F.Scale
theorem _root_.solution {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (g2 g3 : K) (k : ℕ) :
    φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_eq, cW_eq (φ g2) (φ g3) k]
    split_ifs with h2 h3 h4
    · rw [map_div₀, map_ofNat]
    · rw [map_div₀, map_ofNat]
    · rw [map_mul, map_div₀, map_mul, map_add, map_sub, map_mul, map_natCast, map_one, map_sum]
      simp only [map_ofNat]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.isLt
      rw [map_mul, ih (m.val + 2) (by omega), ih (k - (m.val + 2)) (by omega)]
    · exact map_zero φ
end Formalism.L2.Th1.F.Scale
