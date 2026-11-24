-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Lam_monomial_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:27.724614+00:00
-- url     : https://prove2.me/submissions/5c85d755-3719-42c1-bcdd-0d76b927eec2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_coeff_GM
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ne_zero_of_v_eq_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Lam_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_eq_kapC
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_add_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hV : D.Valid v p) {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam)
    (F : MvPolynomial (D.OL × Fin D.r) K) {ζ : D.EM} (hζ : D.LabLowE p ζ) :
    D.abelian₂ p F (monomial ζ 1) =
      D.kapC cst ζ * (D.gaP p gam ζ * (D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ) * (fact ζ : K)) := by
  have h0 : D.ga (D.collapseExponent p ζ) ≠ 0 := ne_zero_of_v_eq_zero (hV.2.2.2.2.2.2.1 _)
  have h1 := D.fact_eq_kapC hdig hζ
  have h2 : (fact (D.phE p ζ) : K) = ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K) *
      (fact (D.collapseExponent p ζ) : K) * (fact (D.tpE ζ) : K) := by
    rw [phE, fact_add_eq]; push_cast; ring
  rw [Lam_monomial, coeff_GM, h2, gaP]
  set B := ((∏ x, (D.collapseExponent p ζ x + D.tpE ζ x).choose (D.tpE ζ x) : ℕ) : K)
  set g := ∏ t, gam t (D.labF ζ t) (D.wF ζ t)
  have h3 : D.kapC cst ζ * (D.ga (D.collapseExponent p ζ) * g * ((D.ga (D.collapseExponent p ζ))⁻¹ *
      (D.ga (D.phE p ζ) * F.coeff (D.phE p ζ) * B)) * (fact ζ : K)) =
      (D.ga (D.phE p ζ) * F.coeff (D.phE p ζ) * B) * (D.kapC cst ζ * g * (fact ζ : K)) := by
    field_simp
  rw [h3, ← h1]; ring
end Formalism.MainNotions.PlaneGram.TwistData
