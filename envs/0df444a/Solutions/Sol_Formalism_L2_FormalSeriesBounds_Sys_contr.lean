-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.contr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:32.87804+00:00
-- url     : https://prove2.me/submissions/48e01561-937a-4ba5-adca-b9edf4947bb3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_coeff_Ps
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_two_le_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow_sub_pow


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
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}
open Formalism.L2.FormalSeriesBounds.Sys
variable (S : Sys X)
namespace Formalism.L2.FormalSeriesBounds.Sys
theorem _root_.solution : Contr S.Ps where
  noConst t c A hA := by
    have hA0 : A.degree = 0 := by omega
    rw [coeff_Ps]
    have : (fun x => dl x A - S.Rr t x A) = (0 : I → C) := by
      funext x
      have h1 : dl (C := C) x A = 0 := by
        unfold dl
        rw [if_neg]
        intro h
        rw [h, Finsupp.degree_single] at hA0
        omega
      have h2 : S.Rr t x A = 0 := by
        unfold Rr
        rw [hA0]
        simp
      simp [h1, h2]
    rw [this, Matrix.zero_vecMul]
    rfl
  contr t t' n ht ht' h b A hA := by
    rw [map_sub, coeff_Ps, coeff_Ps, sub_eq_zero]
    have : (fun x => dl x A - S.Rr t x A) = (fun x => dl x A - S.Rr t' x A) := by
      funext x
      congr 1
      unfold Rr
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => ?_
      have hN := two_le_pow (V := V) s
      have := Formalism.BaseCaseIdentities.OrdGE.pow_sub_pow (ht c) (ht' c) (h c) (N := V.l ^ (s + 1)) (by omega) A
        (by omega)
      rw [map_sub, sub_eq_zero] at this
      rw [this]
    rw [this]
end Formalism.L2.FormalSeriesBounds.Sys
