-- Prove2me | solution 1 for Formalism.DimensionVariation.lift_first_descent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:34.43965+00:00
-- url     : https://prove2.me/submissions/6843a6e3-e90c-4150-a09e-02b3402a4d71

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DimensionVariation_first_descent_product_explicit
import Theorems.Thm_Formalism_DimensionVariation_liftProduct


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : LiftStepDi6 := by
  intro J Pl Emb _ _ _ _ ι Cl Cl' _ _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S kc th0sq γ γ' ε hK
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hS hK0 hkc hth0 hv hmean hOm hSK hth hh hh' hcard hg0
    hm hN hL hLLa hLa h5' h6' hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  exact (first_descent_product_explicit J Pl Emb r ν n (fun j => Fintype.card (ι j))
    (fun j σ => liftNormSq (γ j) (γ' j) (ε j σ)
      (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ)))
    kc Om th0sq (fun j => (Fintype.card (Cl j) : ℝ)) (fun j => (Fintype.card (Cl' j) : ℝ)) hK
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h2 hK0 hkc h10 hth0
    (fun j => Nat.cast_pos.mpr Fintype.card_pos) (fun j => Nat.cast_pos.mpr Fintype.card_pos) hv
    (fun j σ => liftProduct Pl (ι j) (Cl j) (Cl' j) (A j σ) (B j σ) r (ν j) (n j) (s j σ) (Th j σ) (c j σ)
      (Rc j σ) (fun τ => lam τ σ) (fun τ => Om τ σ) (S j σ) (γ j) (γ' j) (ε j σ) (kc j σ) v (th0sq σ)
      (h1 j) (h2 j) (h3 j σ) (h4 j σ) (h5 j σ) (h6 j σ) (h7 j σ) (h8 j σ) (h9 j σ)
      (fun τ => h10 τ σ) (fun τ => h11 τ σ) (h12 j) (h13 j) (h14 j σ) (hS j σ))
    hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5' h6' hT hg p2 p3 p4 p5 p6 p7 p8 hC0).1
end Formalism.DimensionVariation
