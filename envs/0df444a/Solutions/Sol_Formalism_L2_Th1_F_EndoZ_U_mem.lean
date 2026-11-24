-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.U_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:07.934335+00:00
-- url     : https://prove2.me/submissions/91135962-420c-4d2a-8482-55325ae3e76e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ev_notMem
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ev_shift_notMem

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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) : U L P ∈ 𝓝[≠] (0 : ℂ) := by
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := ev_notMem L
  have h2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z + P ∉ L.lattice := nhdsWithin_le_nhds (ev_shift_notMem L hP)
  have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z + -P ∉ L.lattice :=
    nhdsWithin_le_nhds (ev_shift_notMem L hP')
  filter_upwards [h1, h2, h3] with z a b c
  exact ⟨a, b, by simpa [sub_eq_add_neg] using c⟩
end Formalism.L2.Th1.F.EndoZ
