-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.fact_eq_kapC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:38.87588+00:00
-- url     : https://prove2.me/submissions/024471d6-10a8-42fb-86c9-309aa7c42b70

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_EM
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_factorial_embedded_exponent
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_tpE

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
theorem _root_.solution {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) :
    (fact (D.collapseExponent p ζ) : K) * (fact (D.tpE ζ) : K) =
      D.kapC cst ζ * (∏ t, gam t (D.labF ζ t) (D.wF ζ t)) * (fact ζ : K) := by
  have h1 : ∀ t, ((∏ a, (ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a)).factorial : ℕ) : K) =
      cst t (D.labF ζ t) (ldeg ζ (D.mw t)) * ((∏ a, (ζ (D.mw t, a)).factorial : ℕ) : K) *
        gam t (D.labF ζ t) (D.wF ζ t) := fun t => ((hdig.1 t (D.labF ζ t) (hζ t)).2 (D.wF ζ t)).2
  have h0 : ((∏ t : D.Tau, ∏ a, (ζ (D.mlab t, a)).factorial : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun t _ => Finset.prod_ne_zero_iff.mpr fun a _ =>
      Nat.factorial_ne_zero _
  rw [factorial_embedded_exponent, fact_tpE, fact_EM, kapC]
  rw [Nat.cast_mul, Nat.cast_prod (s := (univ : Finset D.Tau))
    (f := fun t => ∏ a, (ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a)).factorial)]
  simp only [h1, Finset.prod_mul_distrib]
  push_cast
  push_cast at h0
  field_simp
end Formalism.MainNotions.PlaneGram.TwistData
