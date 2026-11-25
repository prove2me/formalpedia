-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.gSall_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:27.607545+00:00
-- url     : https://prove2.me/submissions/ed7717a4-ea7c-4635-9161-d79b436bc857

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ} (G : GlW K V n)
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (μ : Fin n → ℤ) :
    G.gS {v | G.IsHW μ v} ≤ ⨆ v : {v // G.IsHW μ v}, G.gS {v.1} := by
  have hgs : ∀ s : Set V, G.Stable (G.gS s) := fun s a b x hx => by
    rw [GlW.gS, Submodule.mem_sInf] at hx ⊢
    exact fun U hU => hU.2 a b x (hx U hU)
  have hstab : G.Stable (⨆ v : {v // G.IsHW μ v}, G.gS {v.1}) := by
    intro a b x hx
    induction hx using Submodule.iSup_induction' with
    | mem i y hy => exact Submodule.mem_iSup_of_mem i (hgs _ a b y hy)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  show sInf {U : Submodule K V | {v | G.IsHW μ v} ⊆ (U : Set V) ∧ G.Stable U} ≤ _
  refine sInf_le ⟨fun v hv => ?_, hstab⟩
  have hv' : v ∈ G.gS {v} := by
    rw [GlW.gS, Submodule.mem_sInf]
    exact fun U hU => hU.1 (Set.mem_singleton v)
  exact Submodule.mem_iSup_of_mem (⟨v, hv⟩ : {v // G.IsHW μ v}) hv'
end Formalism.InvariantFactorPaths.PW
