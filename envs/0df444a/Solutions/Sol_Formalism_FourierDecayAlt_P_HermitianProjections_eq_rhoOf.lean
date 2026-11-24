-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.eq_rhoOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:45.775725+00:00
-- url     : https://prove2.me/submissions/62ad0ba9-c8ad-4f0b-ae53-52fbf8646e1e

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_decomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_rhoOf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_rhoOf_perp

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
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det)
    (g : Matrix n n ℂ) (hg : g * V = V * Φ) (hgU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → g *ᵥ x = x) :
    g = rhoOf H V Φ := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  simp only [Matrix.toLin'_apply]
  have hd := decomp H V hΓ x
  have h1 : g *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x) := hgU _ hd
  have h2 : rhoOf H V Φ *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x) :=
    rhoOf_perp H V Φ _ hd
  have h3 : ∀ w : ι → ℂ, g *ᵥ (V *ᵥ w) = rhoOf H V Φ *ᵥ (V *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg, rhoOf_mul H V Φ hΓ]
  have hx : x = (x - V *ᵥ (prj H V *ᵥ x)) + V *ᵥ (prj H V *ᵥ x) := (sub_add_cancel x _).symm
  rw [hx, Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, h3]
end Formalism.FourierDecayAlt.P.HermitianProjections
