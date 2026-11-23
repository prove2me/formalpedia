-- Prove2me | solution 1 for Comp.ModelData.lStepTr_iterate_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:32.936344+00:00
-- url     : https://prove2.me/submissions/88bf25df-5fb7-4de7-a600-115a112c721c

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_padSat2_bF
import Theorems.Thm_Comp_ModelData_bTr_eq
import Theorems.Thm_Comp_ModelData_aTr_eq
import Theorems.Thm_Comp_ModelData_bTr_inter_enabled1
import Theorems.Thm_Comp_ModelData_aTr_inter_enabled2
import Theorems.Thm_Comp_ModelData_padSat1_lStepF_iterate

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) (k : ℕ) :
    (d.lStepTr hs x y s)^[k] ∅
      = (d.toCsgQ.lStepF x y s)^[k] ∅ ∩ d.enabled1 hs s := by
  induction k with
  | zero =>
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, Finset.empty_inter]
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      unfold lStepTr
      rw [d.bTr_inter_enabled1 hs s _ (d.padSat1_lStepF_iterate hs hnn hnz x y s k) x,
        d.bTr_eq hs hnn hnz _ x s, d.aTr_inter_enabled2 hs s _ y,
        d.aTr_eq hs hnn hnz s _ (d.padSat2_bF hs hnn hnz _ x s) y]
      rfl
end Comp.ModelData
