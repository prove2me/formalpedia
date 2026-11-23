-- Prove2me | solution 1 for Formalism.DimensionVariation.mean_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:03.725435+00:00
-- url     : https://prove2.me/submissions/229fec81-8fd4-4316-ada0-dad9bde6310e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements

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
theorem _root_.solution : MeanDev6 := by
  intro Emb _ _ φ C0 M hφ hM
  have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hS : (∑ s, φ s) = M * (Fintype.card Emb : ℝ) := by rw [hM]; field_simp
  have hM0 : 0 ≤ M + C0 := by
    have : (∑ _s : Emb, (-C0)) ≤ ∑ s, φ s := Finset.sum_le_sum (fun s _ => hφ s)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS] at this
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have hpt : ∀ s, |φ s - M| ≤ (φ s + C0) + (M + C0) := by
    intro s
    have := hφ s
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [div_le_iff₀ hE]
  calc (∑ s, |φ s - M|) ≤ ∑ s, ((φ s + C0) + (M + C0)) := Finset.sum_le_sum (fun s _ => hpt s)
    _ = 2 * (M + C0) * (Fintype.card Emb : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hS, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring
end Formalism.DimensionVariation
