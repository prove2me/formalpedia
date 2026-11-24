-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.sum_Xs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:10:57.720595+00:00
-- url     : https://prove2.me/submissions/e12fe4c2-a15e-4301-a7cc-8bf28de303d0

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
theorem _root_.solution (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), p.val ≤ r + k → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (esI k r c) := by
  symm
  refine Fintype.sum_of_injective (esI k r) ?_ (fun c => g (esI k r c)) g ?_ (fun _ => rfl)
  · intro a b h
    have h1 : 2 * r + k - a.val = 2 * r + k - b.val := congrArg Fin.val h
    have := a.isLt
    have := b.isLt
    exact Fin.ext (by omega)
  · intro p hp
    apply hg
    by_contra h
    have hp2 := p.isLt
    exact hp ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by show 2 * r + k - (2 * r + k - p.val) = p.val; omega)⟩
end Formalism.FourierDecayAlt.P.UnipotentSums
