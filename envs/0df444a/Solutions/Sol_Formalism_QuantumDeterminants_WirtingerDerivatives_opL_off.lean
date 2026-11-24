-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.opL_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:12:37.750166+00:00
-- url     : https://prove2.me/submissions/b6070a6c-6b1d-43c4-a17e-4324588fd292

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∉ OmX m)
    (h0 : g x = 0) : opL k j g x = 0 := by
  match j with
  | 0 => show pOp k g x = 0; simp [pOp, hx]
  | 1 => show x k • g x = 0; rw [h0, smul_zero]
  | 2 => show (x k)⁻¹ • g x = 0; rw [h0, smul_zero]
  | 3 => show pbOp k g x = 0; simp [pbOp, hx]
  | 4 => show star (x k) • g x = 0; rw [h0, smul_zero]
  | 5 => show (star (x k))⁻¹ • g x = 0; rw [h0, smul_zero]
end Formalism.QuantumDeterminants.WirtingerDerivatives
