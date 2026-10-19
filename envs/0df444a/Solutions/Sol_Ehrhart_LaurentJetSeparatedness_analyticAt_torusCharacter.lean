-- Prove2me | solution 1 for Ehrhart.LaurentJetSeparatedness.analyticAt_torusCharacter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/3053abee-858f-4896-9e35-90cffaafc53c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.LaurentJetSeparatedness
open Set Filter Module
open scoped BigOperators Topology
namespace Ehrhart.LaurentJetSeparatedness
theorem _root_.solution {n : ℕ}
    (m : Fin n → ℤ)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ (TorusCharacters.torusCharacter m) p := by
  unfold TorusCharacters.torusCharacter
    TorusCharacters.characterExponent
  apply AnalyticAt.cexp'
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.fun_mul
    ((ContinuousLinearMap.proj i :
      TorusCharacters.LogSpace n →L[ℂ] ℂ).analyticAt p)
end Ehrhart.LaurentJetSeparatedness
