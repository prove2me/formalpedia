-- Prove2me | solution 1 for Formalism.HF.P.quad_not_sq_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:11.309512+00:00
-- url     : https://prove2.me/submissions/8fc03778-567f-49f8-b7bd-3bb77a3cf222

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial Matrix
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by
  intro b hb
  have hsq : IsSquare (a : ℚ) := ⟨b, by rw [← hb]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_intCast_iff.1 hsq
  have hu : IsUnit n := ha n ⟨1, by rw [hn, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (subst h; simp at hn; exact h1 hn)
end Formalism.HF.P
