-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.fil_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:42.071722+00:00
-- url     : https://prove2.me/submissions/b2017dc8-37f3-41b0-9573-3bfc31fcb28e

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution {R Z : Type} [CommRing R] [AddCommGroup Z] [Module R Z] (π : R) (vπ : ℝ)
    (Fil : ℝ → Submodule R Z) (h : ∀ t z, z ∈ Fil t → π • z ∈ Fil (t + vπ)) (k : ℕ) :
    ∀ t z, z ∈ Fil t → π ^ k • z ∈ Fil (t + vπ * (k : ℝ)) := by
  induction k with
  | zero => intro t z hz; simpa using hz
  | succ k ih =>
    intro t z hz
    have h1 := h _ _ (ih t z hz)
    rw [pow_succ', mul_smul]
    convert h1 using 2
    push_cast
    ring
end Formalism.InvariantFactorPaths.G0
