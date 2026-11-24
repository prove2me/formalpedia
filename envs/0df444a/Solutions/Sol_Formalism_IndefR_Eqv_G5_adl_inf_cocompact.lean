-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_inf_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:39.254866+00:00
-- url     : https://prove2.me/submissions/d8bb164b-3db0-4a1a-afb6-d17233d74825

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution : ∃ C : Set (InfiniteAdeleRing F), IsCompact C ∧
    ∀ y, ∃ r : 𝓞 F, y - algebraMap F _ (r : F) ∈ C := by
  classical
  let b := mixedEmbedding.latticeBasis F
  let R : ℝ := ∑ i, ‖b i‖

  have hcoord : ∀ (x : InfiniteAdeleRing F) (w : InfinitePlace F),
      ‖x w‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
    intro x w
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    by_cases hw : w.IsReal
    · refine le_trans ?_ (norm_fst_le _)
      refine le_trans ?_ (norm_le_pi_norm _ ⟨w, hw⟩)
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) (x w)).ge
    · refine le_trans ?_ (norm_snd_le _)
      refine le_trans ?_ (norm_le_pi_norm _ ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩)
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) (x w)).ge
  have hK : ∀ w : InfinitePlace F, IsCompact {z : w.Completion | ‖z‖ ≤ R} := by
    intro w
    have he : {z : w.Completion | ‖z‖ ≤ R} =
        (InfinitePlace.Completion.extensionEmbedding w) ⁻¹' Metric.closedBall 0 R := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff,
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    rw [he]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall 0 R)
  refine ⟨Set.pi Set.univ fun w => {z : w.Completion | ‖z‖ ≤ R}, isCompact_univ_pi hK, ?_⟩
  intro y
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp ((mixedEmbedding.mem_span_latticeBasis (K := F)).mp
    (ZSpan.floor b (InfiniteAdeleRing.ringEquiv_mixedSpace F y)).2)
  refine ⟨r, fun w _ => ?_⟩
  show ‖(y - algebraMap F _ (r : F)) w‖ ≤ R
  refine (hcoord _ w).trans ?_
  rw [map_sub, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have h2 : mixedEmbedding F (r : F) =
      (ZSpan.floor b (InfiniteAdeleRing.ringEquiv_mixedSpace F y) : mixedEmbedding.mixedSpace F) := hr
  rw [h2, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b _
end Formalism.IndefR.Eqv.G5
