-- Prove2me | solution 1 for Formalism.DimensionVariation.liftProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:40.357069+00:00
-- url     : https://prove2.me/submissions/a314954a-f87f-4c3d-9a89-8d1ded73d67f

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Theorems.Thm_Formalism_DimensionVariation_liftOperatorBound


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
theorem _root_.solution
    (Pl ι Cl Cl' : Type) [Fintype Pl] [Fintype ι] [Fintype Cl] [Fintype Cl'] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : Cl → Cl' → (Pl × ι → ℂ) → ℂ) (c : Cl → Cl' → (Pl × ι → ℕ) → ℂ)
    (Rc : (Pl × ι → ℕ) →₀ (A →L[ℂ] B)) (lam : Pl → ℂ) (Om : Pl → ℝ) (S : ℝ)
    (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ) (kc v th0sq : ℝ)
    (h1 : ∀ τ i, 0 ≤ ν τ i) (h2 : ∀ τ, ∑ i, ν τ i = n τ)
    (h3 : ∀ τ u i, 0 ≤ s τ u i) (h4 : ∀ τ u, ∑ i, s τ u i ^ 2 = nsq u)
    (h5 : ∀ L L', Continuous (Th L L'))
    (h6 : ∀ L L' u, HasSum (fun e => c L L' e * mono u e) (Th L L' u))
    (h7 : ∀ L L' u, ‖Th L L' u‖ ≤ S * Real.exp (nsq u / 2))
    (h8 : ∀ e ∈ Rc.support, ∀ τ, ∑ x, e (τ, x) = n τ)
    (h9 : ∀ u, ‖Rc.sum (fun e X => mono (cj u) e • X)‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i)
    (h10 : ∀ τ, 0 < Om τ) (h11 : ∀ τ, ‖lam τ‖ ^ 2 = (Om τ)⁻¹)
    (h12 : ∀ L, 0 < γ L ∧ γ L ≤ 1) (h13 : ∀ L', 0 < γ' L' ∧ γ' L' ≤ 1) (h14 : ∀ L L', ‖ε L L'‖ = 1)
    (hS : S ^ 2 = kc ^ 2 *
          (8 + 32 * ((Fintype.card Pl * Fintype.card ι : ℕ) : ℝ) * v) ^ (Fintype.card Pl * Fintype.card ι) *
          th0sq ^ (Fintype.card Pl * Fintype.card ι)) :
    liftNormSq γ γ' ε (fun L L' => liftBlock (c L L') Rc lam) ≤
      ((Fintype.card Cl : ℝ) * (Fintype.card Cl' : ℝ)) *
      ((kc ^ 2 *
          (8 + 32 * ((Fintype.card Pl * Fintype.card ι : ℕ) : ℝ) * v) ^ (Fintype.card Pl * Fintype.card ι) *
          th0sq ^ (Fintype.card Pl * Fintype.card ι)) *
        ∏ τ, ((Om τ)⁻¹ ^ n τ *
          (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))))) := by
  rw [← hS]
  exact liftOperatorBound Pl ι Cl Cl' A B r ν n s Th c Rc lam Om S γ γ' ε
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
end Formalism.DimensionVariation
