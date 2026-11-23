-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.v_gaP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:25.985796+00:00
-- url     : https://prove2.me/submissions/e5145e8a-2b1a-41ad-b01c-6620b01eab42

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel

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
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) : v (D.gaP p gam ζ) = 0 := by
  unfold gaP
  rw [AddValuation.map_mul, hV.2.2.2.2.2.2.1 (D.collapseExponent p ζ), zero_add]
  exact Finset.prod_induction _ (fun x => v x = 0)
    (fun a b ha hb => by rw [AddValuation.map_mul, ha, hb, add_zero]) (AddValuation.map_one v)
    (fun t _ => ((hdig.1 t (D.labF ζ t) (fun a => hζ t a)).2 (D.wF ζ t)).1)
end Formalism.MainNotions.PlaneGram.TwistData
