-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.liftsAt_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:16.570849+00:00
-- url     : https://prove2.me/submissions/e704149d-17ab-4a63-b319-b469f78660bd

import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_IntegralWachDefinitions
import Theorems.Thm_Formalism_CoboundaryTransfers_gammaStableOfGammaQUnit_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : Mono := by
  intro O A _ _ _ B M M' D _ _ _ _ W hMM' hGQ
  refine ⟨{
    N := W.N
    φ := W.φ
    γ := W.γ
    φ_smul := W.φ_smul
    γ_smul := W.γ_smul
    comm := W.comm
    X_inj := W.X_inj
    Q_bij := W.Q_bij
    φ_N := fun x hx => by
      have h : B.Q ^ M' = B.Q ^ (M' - M) * B.Q ^ M := by
        rw [← pow_add, Nat.sub_add_cancel hMM']
      rw [h, mul_smul]
      exact W.N.smul_mem _ (W.φ_N x hx)
    γ_N := W.γ_N
    γ_QN := gammaStableOfGammaQUnit_holds O A B M' D W.N W.γ hGQ W.Q_bij W.γ_smul W.γ_N }, rfl, rfl, rfl⟩
end Formalism.CoboundaryTransfers
