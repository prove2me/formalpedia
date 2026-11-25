-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.SP_smul_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:32.290947+00:00
-- url     : https://prove2.me/submissions/f21b8cea-ab91-4e3c-865c-7fa6667fdc8b

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
theorem _root_.solution (c : ℂ) {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a (c • b) a' b' := by
  unfold SP at h ⊢
  have e : (fun x => ⟪c • b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) =
      fun x => conj c * (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [inner_smul_left, mul_assoc]
  rw [e]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  rw [h.2, inner_smul_left]
  ring
end Formalism.L2.S.Pv.SchurTens
