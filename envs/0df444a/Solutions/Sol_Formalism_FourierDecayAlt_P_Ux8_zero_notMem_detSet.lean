-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.zero_notMem_detSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:02:25.789363+00:00
-- url     : https://prove2.me/submissions/c11de67e-e92a-4abf-9bf8-468389a44e7b

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution (hD : G.DetMatch) (n : ℕ) (Kc : Set ℂ) (h0 : (0:ℂ) ∉ Kc) : (0:ℂ) ∉ G.detSet n Kc := by
  intro hmem
  simp only [G.detSet, Set.mem_image] at hmem
  obtain ⟨D, hDK, hD0⟩ := hmem
  have hne := (hD n).2
  rcases mul_eq_zero.mp hD0 with h1 | h1
  · exact hne h1
  · exact h0 (by rw [← h1]; exact hDK)
end Formalism.FourierDecayAlt.P.Ux8
