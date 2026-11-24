-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:42.998519+00:00
-- url     : https://prove2.me/submissions/a4918b02-504b-47e2-bf92-ef01b4fcf32a

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n : Type*} [Fintype n]
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution {m ι κ : Type*} [Fintype m] [Fintype ι] [Fintype κ] (H : Matrix m m ℂ)
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    herm H (A *ᵥ a) (B *ᵥ b) = star b ⬝ᵥ ((Bᴴ * H * A) *ᵥ a) := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.HermitianProjections
