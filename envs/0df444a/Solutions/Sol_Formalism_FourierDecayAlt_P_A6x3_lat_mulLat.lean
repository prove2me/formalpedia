-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.lat_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:41.27616+00:00
-- url     : https://prove2.me/submissions/6025ff2f-dba9-4cc0-9396-8db7c64b5370

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (b : Kˣ) {L : AddSubgroup K} (hL : Lat L) : Lat (mulLat (b : K) L) := by
  constructor
  · have : ((mulLat (b : K) L : AddSubgroup K) : Set K) =
        (fun v => ((b⁻¹ : Kˣ) : K) * v) ⁻¹' (L : Set K) := by
      ext v
      simp only [mulLat, AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hv; exact ⟨_, hv, by simp⟩
    rw [this]; exact hL.op.preimage (continuous_const.mul continuous_id)
  · rw [mulLat, AddSubgroup.coe_map]
    exact IsCompact.image hL.cp (continuous_const.mul continuous_id)
end Formalism.FourierDecayAlt.P.A6x3
