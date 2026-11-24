-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.sum_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:44.331732+00:00
-- url     : https://prove2.me/submissions/622c0656-edb5-4cce-af25-1392d036dfbf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentSums
theorem _root_.solution (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), r ≤ p.val → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (eI k r c) := by
  symm
  refine Fintype.sum_of_injective (eI k r) ?_ (fun c => g (eI k r c)) g ?_ (fun _ => rfl)
  · intro a b h
    have h1 : (eI k r a).val = (eI k r b).val := congrArg Fin.val h
    exact Fin.ext h1
  · intro p hp
    apply hg
    by_contra h
    exact hp ⟨⟨p.val, by omega⟩, Fin.ext rfl⟩
end Formalism.FourierDecayAlt.P.UnipotentSums
