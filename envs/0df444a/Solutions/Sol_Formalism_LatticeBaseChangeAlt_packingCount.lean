-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.packingCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:27.306237+00:00
-- url     : https://prove2.me/submissions/76618d74-9f6c-419b-b00a-68a04430c1fc

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial
open MeasureTheory
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : PackingCount := by
  intro n P δ R hδ hδR hR hsep
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero]
    have : P.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => PiLp.ext (fun i => Fin.elim0 i))
    exact_mod_cast this
  · haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
    classical
    have hd2 : 0 < δ / 2 := by linarith
    have hV0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume _ one_pos).ne'
    have hVt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hball : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 ≤ ρ →
        volume (Metric.ball x ρ) = ENNReal.ofReal (ρ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      intro x ρ hρ
      rw [Measure.addHaar_ball _ _ hρ, finrank_euclideanSpace_fin]
    have hdisj : Set.PairwiseDisjoint (↑P : Set (EuclideanSpace ℝ (Fin n))) (fun x => Metric.ball x (δ / 2)) := by
      intro x hx y hy hxy
      exact Metric.ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
    have hsub : (⋃ x ∈ P, Metric.ball x (δ / 2)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2) := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, hx, hz⟩ := hz
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := norm_le_norm_add_norm_sub' z x
      linarith [hR x hx]
    have hmeas : volume (⋃ x ∈ P, Metric.ball x (δ / 2)) = ∑ x ∈ P, volume (Metric.ball x (δ / 2)) :=
      measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)
    have key : ∑ x ∈ P, volume (Metric.ball x (δ / 2))
        ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2)) := by
      rw [← hmeas]
      exact measure_mono hsub
    simp only [hball _ _ hd2.le, hball _ _ (by linarith : (0:ℝ) ≤ R + δ / 2), Finset.sum_const,
      nsmul_eq_mul] at key
    rw [← mul_assoc] at key
    have key2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 key
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) n)] at key2
    have hfin : (R + δ / 2) ^ n ≤ (3 * R / δ) ^ n * (δ / 2) ^ n := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by linarith)
      have e : 3 * R / δ * (δ / 2) = 3 * R / 2 := by
        field_simp
      rw [e]
      linarith
    exact le_of_mul_le_mul_right (key2.trans hfin) (pow_pos hd2 n)
end Formalism.LatticeBaseChangeAlt
