-- Prove2me | solution 1 for Ehrhart.LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/1d1dc691-4579-44ec-91e4-f1a82aa5ab41

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_LaurentJetSeparatedness_analyticAt_torusCharacter

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
theorem _root_.solution {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ
      (AdaptedBergmanBasis.normalizedHolomorphicMonomial
        K hk φ u) p := by
  unfold AdaptedBergmanBasis.normalizedHolomorphicMonomial
  exact analyticAt_const.fun_mul
    (analyticAt_torusCharacter
      (WeightedTorusHilbert.integerExponent K hk u) p)
end Ehrhart.LaurentJetSeparatedness
