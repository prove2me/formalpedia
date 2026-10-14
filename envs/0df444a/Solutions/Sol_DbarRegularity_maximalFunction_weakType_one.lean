-- Prove2me | solution 1 for DbarRegularity.maximalFunction_weakType_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T22:27:26.295474+00:00
-- url     : https://prove2.me/submissions/7eb639bc-d646-4f93-bb9b-e5fbec94b856

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Covering.Vitali



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Scaling of ball volumes in `ℝ^d`. -/
lemma volume_ball_mul {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hc : 0 < c) :
    volume (ball x (c * r)) = ENNReal.ofReal c ^ d * volume (ball x r) := by
  rw [Measure.addHaar_ball_of_pos _ _ (by positivity), Measure.addHaar_ball_of_pos _ _ hr,
    finrank_euclideanSpace_fin, mul_pow, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hc.le, mul_assoc]

/-- Radii realising the maximal function above `α`, with a uniform bound. -/
lemma exists_radius_bound {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0) (hα : 0 < α)
    (hS : ∫⁻ y, ‖f y‖ₑ ≠ ⊤) :
    ∃ R : ℝ, ∀ x, (α : ℝ≥0∞) < maximalFunction f x → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      (α : ℝ≥0∞) * volume (ball x ρ) < ∫⁻ y in ball x ρ, ‖f y‖ₑ := by
  have key : ∀ x, (α : ℝ≥0∞) < maximalFunction f x → ∃ ρ : ℝ, 0 < ρ ∧
      (α : ℝ≥0∞) * volume (ball x ρ) < ∫⁻ y in ball x ρ, ‖f y‖ₑ := by
    intro x hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.1 hx
    obtain ⟨hr0, hr⟩ := lt_iSup_iff.1 hr
    refine ⟨r, hr0, ?_⟩
    have h0 : volume (ball x r) ≠ 0 := (measure_ball_pos _ _ hr0).ne'
    have ht : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
    rw [← ENNReal.div_eq_inv_mul] at hr
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl ht)).1 hr
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, fun x hx => ?_⟩
    obtain ⟨r, hr0, hr⟩ := key x hx
    have hb : ∀ s : ℝ, 0 < s → ball x s = univ := fun s hs =>
      eq_univ_of_forall fun y => by
        rw [mem_ball, Subsingleton.elim y x, dist_self]; exact hs
    refine ⟨1, one_pos, le_rfl, ?_⟩
    rwa [hb 1 one_pos, ← hb r hr0]
  set c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hc0 : c ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hct : c ≠ ⊤ := measure_ball_lt_top.ne
  set K := ((∫⁻ y, ‖f y‖ₑ) / ((α : ℝ≥0∞) * c)).toReal
  refine ⟨max 1 K, fun x hx => ?_⟩
  obtain ⟨r, hr0, hr⟩ := key x hx
  refine ⟨r, hr0, ?_, hr⟩
  have hlt : (α : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * c) < ∫⁻ y, ‖f y‖ₑ := by
    have hB : volume (ball x r) = ENNReal.ofReal (r ^ d) * c := by
      rw [Measure.addHaar_ball_of_pos _ _ hr0, finrank_euclideanSpace_fin]
    rw [← hB]
    exact hr.trans_le (setLIntegral_le_lintegral _ _)
  have hαc0 : (α : ℝ≥0∞) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hα.ne') hc0
  have hαct : (α : ℝ≥0∞) * c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hct
  have h1 : ENNReal.ofReal (r ^ d) < (∫⁻ y, ‖f y‖ₑ) / ((α : ℝ≥0∞) * c) := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hαc0) (Or.inl hαct)]
    calc ENNReal.ofReal (r ^ d) * ((α : ℝ≥0∞) * c)
        = (α : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * c) := by ring
      _ < _ := hlt
  have h2 : r ^ d < K := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (ENNReal.div_ne_top hS hαc0)] at h1
    exact h1
  rcases le_or_gt r 1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact (le_self_pow₀ h.le hd.ne').trans (h2.le.trans (le_max_right _ _))

/-- Weak type `(1,1)` bound for the Hardy–Littlewood maximal function, with constant `5^d`. -/
theorem maximalFunction_weakType_one (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ x, ‖f x‖ₑ := by
  by_cases hS : ∫⁻ y, ‖f y‖ₑ = ⊤
  · rw [hS, ENNReal.mul_top]
    · exact le_top
    · exact ENNReal.div_ne_zero.2 ⟨pow_ne_zero _ (by norm_num), ENNReal.coe_ne_top⟩
  obtain ⟨R, hR⟩ := exists_radius_bound f α hα hS
  set E := {x | (α : ℝ≥0∞) < maximalFunction f x}
  choose! ρ hρ0 hρR hρ using hR
  obtain ⟨u, huE, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    E id ρ R (fun a ha => hρR a ha) 5 (by norm_num)
  have hu : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a ha => nonempty_ball.2 (hρ0 a (huE ha)))
  have hsub : E ⊆ ⋃ b ∈ u, ball b (5 * ρ b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact mem_biUnion hb (hab (mem_ball_self (hρ0 a ha)))
  haveI : Countable u := hu.to_subtype
  have hvol : ∀ b ∈ u, volume (ball b (5 * ρ b)) ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ y in ball b (ρ b), ‖f y‖ₑ := by
    intro b hb
    have hV := hρ b (huE hb)
    calc volume (ball b (5 * ρ b)) = (5 : ℝ≥0∞) ^ d * volume (ball b (ρ b)) := by
          rw [volume_ball_mul b (hρ0 b (huE hb)) 5 (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ (5 : ℝ≥0∞) ^ d * ((∫⁻ y in ball b (ρ b), ‖f y‖ₑ) / α) := by
          gcongr
          rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hα.ne'))
            (Or.inl ENNReal.coe_ne_top), mul_comm]
          exact hV.le
      _ = _ := by rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
  calc volume E ≤ volume (⋃ b ∈ u, ball b (5 * ρ b)) := measure_mono hsub
    _ ≤ ∑' b : u, volume (ball (b : EuclideanSpace ℝ (Fin d)) (5 * ρ b)) :=
        measure_biUnion_le _ hu _
    _ ≤ ∑' b : u, (5 : ℝ≥0∞) ^ d / α * ∫⁻ y in ball (b : EuclideanSpace ℝ (Fin d)) (ρ b),
          ‖f y‖ₑ := ENNReal.tsum_le_tsum fun b => hvol b b.2
    _ = (5 : ℝ≥0∞) ^ d / α * ∫⁻ y in ⋃ b : u, ball (b : EuclideanSpace ℝ (Fin d)) (ρ b),
          ‖f y‖ₑ := by
        rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun _ => measurableSet_ball)]
        intro i j hij
        exact hdisj i.2 j.2 (Subtype.coe_injective.ne hij)
    _ ≤ (5 : ℝ≥0∞) ^ d / α * ∫⁻ y, ‖f y‖ₑ := by
        exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ x, ‖f x‖ₑ :=
  maximalFunction_weakType_one d f α hα
