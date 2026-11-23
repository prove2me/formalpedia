-- Prove2me | solution 1 for Formalism.FX.rectRes_edge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:05.565254+00:00
-- url     : https://prove2.me/submissions/24075607-8aa5-4424-a53d-f1269b2635cd

import Definitions.Def_Formalism_LFunctionBounds_ExpSumLowerBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.FX
namespace Formalism.FX
theorem _root_.solution (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
  have hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P := fun t ht hmem => hP t ht _ hmem rfl
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c) := fun p hp =>
    continuousOn_const.div (hγ.continuousOn.sub continuousOn_const)
      (fun t ht => sub_ne_zero.2 (hP t ht p hp))
  calc ∫ t in a..c, g (γ t)
      = ∫ t in a..c, (G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))
        rw [hg _ (hγP t ht)]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [mul_one_div]
    _ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by
        refine intervalIntegral.integral_add hG.intervalIntegrable ?_
        exact (continuousOn_finset_sum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable
    _ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
        rw [intervalIntegral.integral_finset_sum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro p hp
          exact ((hcont p hp).intervalIntegrable).const_mul (b p)
end Formalism.FX
