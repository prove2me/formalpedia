-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.SP_add_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:59.685501+00:00
-- url     : https://prove2.me/submissions/7b21b137-cb9f-4e80-9808-13154428b923

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution {a b₁ b₂ a' b' : Hs} (h₁ : SP m σs D a b₁ a' b') (h₂ : SP m σs D a b₂ a' b') :
    SP m σs D a (b₁ + b₂) a' b' := by
  unfold SP at h₁ h₂ ⊢
  have e : (fun x => ⟪b₁ + b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => ⟪b₁, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ + ⟪b₂, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ := by
    funext x
    rw [inner_add_left, add_mul]
  rw [e]
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2, inner_add_left]
  ring
end Formalism.L2.S.Pv.SchurTens
