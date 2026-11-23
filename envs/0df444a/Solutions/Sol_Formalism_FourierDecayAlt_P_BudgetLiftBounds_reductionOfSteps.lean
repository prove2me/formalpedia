-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.reductionOfSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:01.484803+00:00
-- url     : https://prove2.me/submissions/d62cbeb3-eebb-4516-b852-3d205ff706b9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_isPt_PT
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_le_wsup
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_le_sq_sqrt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BudgetLiftBounds_slev_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BudgetLiftBounds
namespace Formalism.FourierDecayAlt.P.BudgetLiftBounds
theorem _root_.solution : ReductionOfSteps := by
  intro hOL hEps hA4 hJ C₀ hC₀
  obtain ⟨C'J, CJ, hJ'⟩ := hJ C₀ hC₀
  refine ⟨max C'J 1, CJ, ?_⟩
  intro E _ _ H _ _ _ W _ len Kl f Θ D Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 hA13 hE hSz hEst hEn hw0 hV hRow hSum
  have hΘJ : C'J ≤ Θ := le_trans (le_max_left _ _) hΘ
  have hΘ1 : 1 ≤ Θ := le_trans (le_max_right _ _) hΘ
  have hΘ0 : 0 < Θ := by linarith
  have hC0 : 0 < C₀ := by linarith
  have hep0 : 0 ≤ (C₀ * Θ ^ (-((Kl : ℝ) - 5 / 2))) ^ f := by positivity
  have ha0 : 0 ≤ (C₀ / Θ) ^ f := by positivity
  have main : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → ∀ eps : ℝ, 0 < eps →
      (gram (D.K (D.r + 1)) (Φ eps w0) (PT Sg (D.r + 1))).re ≤
        ((1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) *
          wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
    intro Sg hNZ eps heps
    have hrec := hJ' (Kl : ℝ) Θ f D.r (fun i => max (D.e i) 0)
      (fun i => √(lsup D len Kl Sg (Φ eps) i))
      (by exact_mod_cast hKl) hf hΘJ hr (fun i => le_max_right _ _) (fun i => Real.sqrt_nonneg _)
      (by
        intro i h1 hi
        have h := hOL E H W len Kl D Sg (Φ eps) (tr eps i) Pat1 Pat3 (pat1 i) (pat3 i) (c1 i) (c3 i)
          (ep1 i) (ep3 i) (bd4 i) _ _ i hNZ h1 hi hep0 ha0 hK hA2 hA13 hE
          (hEst eps heps i (mem_Icc.mpr ⟨h1, hi⟩)) (hSz i (mem_Icc.mpr ⟨h1, hi⟩))
        have he : max (D.e i) 0 = D.e i := max_eq_left (hE i h1 hi).1
        simp only [he]
        exact h)
    have hprod : (∏ i ∈ Icc 1 (D.r + 1), (1 + max (D.e i) 0)) = ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      obtain ⟨h1, h2⟩ := mem_Icc.mp hi
      rw [max_eq_left (hE i h1 h2).1]
    rw [hprod] at hrec
    have h0 : lsup D len Kl Sg (Φ eps) 0 =
        wsup len (4 * Kl * (D.r + 1)) (fun w => ‖Φ eps w []‖ ^ 2) := by
      unfold lsup
      rw [Nat.sub_zero]
      congr 1
      funext w
      exact slev_zero D Sg (Φ eps) w hK.1
    have h0nn : 0 ≤ lsup D len Kl Sg (Φ eps) 0 := by
      rw [h0]
      exact le_trans (sq_nonneg _)
        (le_wsup len _ (fun w => ‖Φ eps w []‖ ^ 2) w0 (by rw [hw0]; exact Nat.zero_le _))
    rw [Real.sq_sqrt h0nn, h0] at hrec
    have htop : Slev D Sg (Φ eps) w0 (D.r + 1) ≤ lsup D len Kl Sg (Φ eps) (D.r + 1) :=
      le_wsup len _ (fun w => Slev D Sg (Φ eps) w (D.r + 1)) w0 (by rw [hw0]; exact Nat.zero_le _)
    exact le_trans htop (le_trans (le_sq_sqrt _) hrec)
  have lim : ∀ Sg : ℕ → ℕ → Finset E, NZSg Sg → (gram (D.K (D.r + 1)) V (PT Sg (D.r + 1))).re ≤
      ((1 + CJ * ((D.r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i))) * jn := by
    intro Sg hNZ
    exact hEps E H W len (D.K (D.r + 1)) (PT Sg (D.r + 1)) Φ V w0 (4 * Kl * (D.r + 1)) _ jn
      (by rw [hw0]; exact Nat.zero_le _) (main Sg hNZ) hEn
      (fun p hp => hV p (isPt_PT Sg hNZ _ p hp))
  exact hA4 E H (D.r + 1) (D.K (D.r + 1)) V ρ c _ lim hRow hSum
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
