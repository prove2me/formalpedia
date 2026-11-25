-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.SP_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:19.148396+00:00
-- url     : https://prove2.me/submissions/7527aaf3-4af6-4a59-bf2c-3e8d5a3ed40b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Theorems.Thm_P2M_Formalism_L2_S_Pv_SchurTens_integrable_conj__b586f57a26e4

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
theorem _root_.solution {a b a' b' : Hs} (h : SP m σs D a b a' b') : SP m σs D a' b' a b := by
  unfold SP at h ⊢
  have e : (fun x => ⟪b', σs x a'⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => conj (⟪b, σs x a⟫_ℂ * conj ⟪b', σs x a'⟫_ℂ) := by
    funext x
    rw [map_mul, Complex.conj_conj]
    ring
  rw [e]
  refine ⟨integrable_conj' h.1, ?_⟩
  rw [integral_conj, h.2]
  rw [map_div₀, map_mul, Complex.conj_ofReal, inner_conj_symm, inner_conj_symm]
end Formalism.L2.S.Pv.SchurTens
