-- Prove2me | solution 1 for EdenVerified.s02_common_index_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:08.587937+00:00
-- url     : https://prove2.me/submissions/43098ce3-39b9-425a-affb-ce446dc6d6e1

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_commonIndexDimension_eq_target
import Theorems.Thm_Eden_commonIndexLocalDimension_eq
import Theorems.Thm_Eden_commonIndexLocalDimension_eq_target_iff
import Theorems.Thm_Eden_commonIndexLocalDimension_isGreatest


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    (∀ p : PhaseSpace, commonIndexLocalDimension c p =
      4 + spectrumPartialSum (lyapunovExponent c p) 4 / c) ∧
    commonIndexDimension c = 4 + 4/c ∧
    IsGreatest (commonIndexLocalDimension c '' attractor) (4 + 4/c) ∧
    (∀ p ∈ attractor, commonIndexLocalDimension c p = 4 + 4/c ↔ p ∈ torus) :=
  ⟨commonIndexLocalDimension_eq hc, commonIndexDimension_eq_target hc,
    commonIndexLocalDimension_isGreatest hc,
    fun p hp => commonIndexLocalDimension_eq_target_iff hc hp⟩
end EdenVerified
