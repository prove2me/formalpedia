-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantReindex.perm_of_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:10.735151+00:00
-- url     : https://prove2.me/submissions/d574290c-ff3e-4cef-8d1e-de8890607ce3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.DeterminantReindex
open C2x2 CardInsertEmbedding
namespace Formalism.FourierDecayAlt.P.DeterminantReindex
theorem _root_.solution {m k : ℕ} (e ρ : Fin k → Fin m) (he : Function.Injective e)
    (hr : ∀ t, ∃ s, ρ s = e t) : ∃ τ : Equiv.Perm (Fin k), ∀ t, e t = ρ (τ t) := by
  choose τ' hτ' using hr
  have hinj : Function.Injective τ' := by
    intro x y hxy; apply he; rw [← hτ' x, ← hτ' y, hxy]
  refine ⟨Equiv.ofBijective τ' (Finite.injective_iff_bijective.mp hinj), fun t => ?_⟩
  simp [hτ']
end Formalism.FourierDecayAlt.P.DeterminantReindex
