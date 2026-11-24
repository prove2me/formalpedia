-- Prove2me | solution 1 for Formalism.SA.P.card_le_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:34.740098+00:00
-- url     : https://prove2.me/submissions/b94dabfd-5db7-439b-bd3b-c926e798c4f6

import Definitions.Def_Formalism_LatticeRigidity_PackCount
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PackingCountGeometricMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Module
open Formalism Formalism.SA Formalism.SA.P
namespace Formalism.SA.P
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} (S : Finset α) (g : α → E) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lam ≤ ‖g x - g y‖)
    (hbd : ∀ x ∈ S, ‖g x‖ ≤ R) :
    (S.card : ℝ) ≤ (1 + 2 * R / lam) ^ finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar with hμ
  have hr : 0 < lam / 2 := by positivity
  have hR2 : 0 < R + lam / 2 := by positivity
  have hdisj : Set.PairwiseDisjoint (↑S : Set α) (fun x => ball (g x) (lam / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hz1 hz2
    simp only [mem_ball, dist_eq_norm] at hz1 hz2
    have h1 := hsep x hx y hy hxy
    have h2 : ‖g x - g y‖ < lam := by
      calc ‖g x - g y‖ = ‖(z - g y) - (z - g x)‖ := by congr 1; abel
        _ ≤ ‖z - g y‖ + ‖z - g x‖ := norm_sub_le _ _
        _ < lam / 2 + lam / 2 := add_lt_add hz2 hz1
        _ = lam := by ring
    linarith
  have hsub : (⋃ x ∈ S, ball (g x) (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    simp only [mem_ball, dist_eq_norm, sub_zero] at hz ⊢
    calc ‖z‖ = ‖(z - g x) + g x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - g x‖ + ‖g x‖ := norm_add_le _ _
      _ < lam / 2 + R := add_lt_add_of_lt_of_le hz (hbd x hx)
      _ = R + lam / 2 := by ring
  have hball : ∀ c : E, ∀ r : ℝ, 0 < r →
      μ (ball c r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) :=
    fun c r hr' => Measure.addHaar_ball_of_pos μ c hr'
  have hb1 : ∀ x, μ (ball (g x) (lam / 2)) =
      ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1) := fun x => hball _ _ hr
  have hV0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hVtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have key : (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + lam / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = ∑ x ∈ S, μ (ball (g x) (lam / 2)) := by
          simp only [hb1, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = μ (⋃ x ∈ S, ball (g x) (lam / 2)) :=
          (measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)).symm
      _ ≤ μ (ball 0 (R + lam / 2)) := measure_mono hsub
      _ = _ := hball 0 _ hR2
  have key2 : (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + lam / 2) ^ finrank ℝ E) := by
    exact (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp key
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at key2
  have key3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key2
  have hpos : 0 < (lam / 2) ^ finrank ℝ E := pow_pos hr _
  have hq : 1 + 2 * R / lam = (R + lam / 2) / (lam / 2) := by
    first
    | (field_simp; done)
    | (field_simp; ring)
  rw [hq, div_pow, le_div_iff₀ hpos]
  exact key3
end Formalism.SA.P
