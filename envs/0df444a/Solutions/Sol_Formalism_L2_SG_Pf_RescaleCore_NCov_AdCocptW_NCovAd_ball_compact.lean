-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW.NCovAd_ball_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:25.682216+00:00
-- url     : https://prove2.me/submissions/f6db0c77-6e35-4242-b2d9-4677189f2749

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CompactCovering_NCovAd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RescaleCore Formalism.L2.SG.Pf.RescaleCore.NCov
open Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
theorem _root_.solution (v : InfinitePlace F) (R : ℝ) :
    IsCompact (closedBall (0 : v.Completion) R) := by
  first
  | exact isCompact_closedBall (0 : v.Completion) R
  | exact (haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
      isCompact_closedBall (0 : v.Completion) R)
  | exact (by
      have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v
      have hc := (hi.isClosedEmbedding).isCompact_preimage (isCompact_closedBall (0 : ℂ) R)
      have e : (NumberField.InfinitePlace.Completion.extensionEmbedding v) ⁻¹' closedBall 0 R =
          closedBall (0 : v.Completion) R := by
        ext z
        simp only [Set.mem_preimage, mem_closedBall, dist_zero_right]
        rw [hi.norm_map_of_map_zero (map_zero _)]
      rw [e] at hc
      exact hc)
end Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
