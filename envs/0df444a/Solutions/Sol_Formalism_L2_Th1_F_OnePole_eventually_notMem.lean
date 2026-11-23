-- Prove2me | solution 1 for Formalism.L2.Th1.F.OnePole.eventually_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:31.129614+00:00
-- url     : https://prove2.me/submissions/1d5b928f-700b-4f67-884d-bac9b3fb7fd9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_AnalyticIdentityTheoremsZetaFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_OnePole
import Theorems.Thm_Formalism_L2_Th1_F_OnePole_tendsto_add_nhdsNE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.OnePole
open AnalyticIdentityTheoremsZetaFacts
namespace Formalism.L2.Th1.F.OnePole
theorem _root_.solution (L : PeriodPair) (p z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w - p ∉ L.lattice := by
  have hx : ∀ x : ℂ, ∀ᶠ u in 𝓝[≠] x, u ∉ L.lattice := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have hd : DiscreteTopology (L.lattice : Set ℂ) := (inferInstance : DiscreteTopology L.lattice)
      exact Filter.inf_principal_eq_bot.1 ((discreteTopology_subtype_iff.1 hd) x hx)
    · exact eventually_nhdsWithin_of_eventually_nhds ((L.isClosed_lattice.isOpen_compl).mem_nhds hx)
  have := (tendsto_add_nhdsNE z (-p)).eventually (hx (z + -p))
  simpa [sub_eq_add_neg] using this
end Formalism.L2.Th1.F.OnePole
