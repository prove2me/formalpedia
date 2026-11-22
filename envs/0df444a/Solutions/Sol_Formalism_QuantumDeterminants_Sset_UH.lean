-- Prove2me | solution 1 for Formalism.QuantumDeterminants.Sset_UH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:39.791557+00:00
-- url     : https://prove2.me/submissions/77a6c901-2216-4486-a75c-b0756e1c3104

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have h2 : mᴴ * Hpk k r * m = Hpk k r := hm.1
  rw [conjTranspose_mul]
  calc mᴴ * hᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2]
end Formalism.QuantumDeterminants
