-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentUpperFacts.agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:52.20406+00:00
-- url     : https://prove2.me/submissions/1d618bfa-9339-4328-b94d-ad25a1b7a5bb

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_decomp


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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.UnipotentUpperFacts
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (A B : Matrix n n ℂ)
    (hV : A * V = B * V) (hU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → A *ᵥ x = B *ᵥ x) : A = B := by
  have hV' : ∀ y, A *ᵥ (V *ᵥ y) = B *ᵥ (V *ᵥ y) := by
    intro y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hV]
  have key : ∀ x, A *ᵥ x = B *ᵥ x := by
    intro x
    have hd := decomp H V hΓ x
    have ex : x = V *ᵥ (prj H V *ᵥ x) + (x - V *ᵥ (prj H V *ᵥ x)) := by abel
    rw [ex, Matrix.mulVec_add, Matrix.mulVec_add, hU _ hd, hV']
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this
end Formalism.FourierDecayAlt.P.UnipotentUpperFacts
