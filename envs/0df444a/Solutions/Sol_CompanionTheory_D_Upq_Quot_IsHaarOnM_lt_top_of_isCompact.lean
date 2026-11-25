-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:31.059582+00:00
-- url     : https://prove2.me/submissions/07d39dbd-aaa1-4db3-befd-3e84ee5860b2

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Theorems.Thm_CompanionTheory_D_Upq_Quot_finiteOnCompacts_of_sigmaFinite
import Theorems.Thm_CompanionTheory_D_Upq_Quot_map_comap_toM
import Theorems.Thm_CompanionTheory_D_Upq_Quot_comap_map_mul
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_measurableEmbedding_toM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
open PI CompanionTheory.D.Upq.ModEx
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}
namespace CompanionTheory.D.Upq.Quot
namespace IsHaarOnM
theorem _root_.solution (hG : IsMatGroup G) {μ : Measure (MtM m)}
    (hμ : IsHaarOnM G μ) {K : Set (MtM m)} (hK : IsCompact K) : μ K < ∞ := by
  obtain ⟨hσ, -, h0, hl⟩ := hμ
  have hι := MG.measurableEmbedding_toM (hG := hG)
  have hmap := map_comap_toM hG h0
  haveI : T2Space (MG G hG) := MG.isClosedEmbedding_mat.isEmbedding.t2Space
  haveI : SigmaFinite (μ.comap (MG.toM (hG := hG))) :=
    SigmaFinite.of_map _ hι.measurable.aemeasurable (by rwa [hmap])
  haveI : IsMulLeftInvariant (μ.comap (MG.toM (hG := hG))) :=
    ⟨fun g => comap_map_mul hG h0 g (hl _ g.mem)⟩
  haveI := finiteOnCompacts_of_sigmaFinite (μ.comap (MG.toM (hG := hG)))
  rw [← hmap, hι.map_apply]
  exact ((MG.isClosedEmbedding_mat (hG := hG)).isCompact_preimage hK).measure_lt_top
end IsHaarOnM
end CompanionTheory.D.Upq.Quot
