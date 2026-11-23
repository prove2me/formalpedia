-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.tTerm_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:25.111602+00:00
-- url     : https://prove2.me/submissions/c12f3e79-d28b-4fb6-a3a2-e6ccd32cdcef

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K]
open Classical
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (R : Subring K) (ψ : AddChar K ℂ) {m m' N N' : ℕ} (hN : N = m + 1)
    (hN' : N' = m' + 1) (Z₁ : Matrix (Fin m) (Fin m) K) (Z₂ : Matrix (Fin m') (Fin m') K) (c : K)
    (x y : Fin m → KR R) (x' y' : Fin m' → KR R) :
    tTerm R ψ hN hN' Z₁ Z₂ c ((x, y), (x', y')) =
      (if IsInt R (bigZ hN Z₁ (outV R x) (outV R y) c) ∧
          IsInt R (bigZ hN' Z₂ (outV R x') (outV R y') c) then
        (Nat.card (isoZZ R (bigZ hN Z₁ (outV R x) (outV R y) c)
          (bigZ hN' Z₂ (outV R x') (outV R y') c)) : ℂ) else 0) *
        ψ (lastE (outV R x) + lastE (outV R y)) *
        conj (ψ (lastE (outV R x') + lastE (outV R y'))) := rfl
end Formalism.FourierDecayAlt.P.A5x8
