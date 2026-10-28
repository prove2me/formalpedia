-- Prove2me | solution 1 for CoherenceTracking.Dephasing.eq_37_38
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:35:55.731916+00:00
-- url     : https://prove2.me/submissions/567edc2a-2f1f-4220-a29a-476841b1ce84

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

open CoherenceTracking.Dephasing Filter Topology in
theorem solution (γ : ℝ) (hγ : 0 < γ) (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ)
    (hv : SolvesBloch γ ω v T) (hc : 0 < initCoherence (v 0))
    (hcoh : ∀ t ∈ Set.Ico 0 T, initCoherence (v t) = initCoherence (v 0)) :
    (∀ t ∈ Set.Ico 0 T,
        v t 2 = Real.sign (v 0 2) * √(v 0 2 ^ 2 - 2 * γ * initCoherence (v 0) * t)) ∧
    T ≤ breakdownTime γ (v 0) := by
  set c0 := initCoherence (v 0) with hc0
  obtain ⟨hcont, hder⟩ := hv
  have hcomp : ∀ i : Fin 3, ContinuousOn (fun s => v s i) (Set.Ico 0 T) := fun i =>
    (continuous_apply i).comp_continuousOn hcont
  -- Bloch equation components
  have hrow : ∀ (w : Fin 3 → ℝ) (u : BVec),
      (blochMatrix γ w).mulVec u = ![-γ * u 0 - w 0 * u 1 - w 2 * u 2,
        w 0 * u 0 - γ * u 1 - w 1 * u 2, w 2 * u 0 + w 1 * u 1] := by
    intro w u
    funext i
    fin_cases i <;> simp [blochMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have hdi : ∀ t ∈ Set.Ioo 0 T, ∀ i : Fin 3,
      HasDerivAt (fun s => v s i) ((blochMatrix γ (ω t)).mulVec (v t) i) t := fun t ht i =>
    (hasDerivAt_pi.mp (hder t ht)) i
  -- derivative of v₂² + 2γc₀ t vanishes
  have hg : ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun s => v s 2 ^ 2 + 2 * γ * c0 * s) 0 t := by
    intro t ht
    have h0 := hdi t ht 0
    have h1 := hdi t ht 1
    have h2 := hdi t ht 2
    rw [hrow] at h0 h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0 h1 h2
    -- coherence is locally constant
    have hcd : HasDerivAt (fun s => v s 0 ^ 2 + v s 1 ^ 2)
        (2 * v t 0 * (-γ * v t 0 - ω t 0 * v t 1 - ω t 2 * v t 2) +
          2 * v t 1 * (ω t 0 * v t 0 - γ * v t 1 - ω t 1 * v t 2)) t := by
      exact ((h0.pow 2).add (h1.pow 2)).congr_deriv (by push_cast; ring)
    have hloc : (fun s => v s 0 ^ 2 + v s 1 ^ 2) =ᶠ[𝓝 t] fun _ => c0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      have := hcoh s ⟨hs.1.le, hs.2⟩
      unfold initCoherence at this
      rw [this]
    have hcd0 : HasDerivAt (fun s => v s 0 ^ 2 + v s 1 ^ 2) 0 t :=
      (hasDerivAt_const t c0).congr_of_eventuallyEq hloc
    have huniq := hcd.unique hcd0
    have hct : v t 0 ^ 2 + v t 1 ^ 2 = c0 := hcoh t ⟨ht.1.le, ht.2⟩
    have hsq := (h2.pow 2).add ((hasDerivAt_id t).const_mul (2 * γ * c0))
    refine hsq.congr_deriv ?_
    push_cast
    linear_combination -huniq - 2 * γ * hct
  -- v₂(t)² = v₂(0)² - 2γc₀t
  have hsq : ∀ t ∈ Set.Ico 0 T, v t 2 ^ 2 = v 0 2 ^ 2 - 2 * γ * c0 * t := by
    intro t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · rw [← h0]; ring
    · have hfc : ContinuousOn (fun s => v s 2 ^ 2 + 2 * γ * c0 * s) (Set.Icc 0 t) := by
        refine ((hcomp 2).pow 2 |>.add (continuousOn_const.mul continuousOn_id)).mono ?_
        intro s hs; exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      obtain ⟨d, hd, hdeq⟩ := exists_hasDerivAt_eq_slope (fun s => v s 2 ^ 2 + 2 * γ * c0 * s)
        (fun _ => (0 : ℝ)) hpos hfc (fun x hx => hg x ⟨hx.1, lt_trans hx.2 ht.2⟩)
      have : (v t 2 ^ 2 + 2 * γ * c0 * t) - (v 0 2 ^ 2 + 2 * γ * c0 * 0) = 0 := by
        have hne : t - 0 ≠ 0 := by linarith
        have := hdeq.symm
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h hne
      linarith
  have htb : breakdownTime γ (v 0) = v 0 2 ^ 2 / (2 * γ * c0) := rfl
  have hden : 0 < 2 * γ * c0 := by positivity
  have hTle : T ≤ breakdownTime γ (v 0) := by
    by_contra hlt
    push_neg at hlt
    rw [htb] at hlt
    have htb0 : 0 ≤ v 0 2 ^ 2 / (2 * γ * c0) := by positivity
    set t := (v 0 2 ^ 2 / (2 * γ * c0) + T) / 2
    have ht1 : v 0 2 ^ 2 / (2 * γ * c0) < t := by simp only [t]; linarith
    have ht2 : t < T := by simp only [t]; linarith
    have h := hsq t ⟨by linarith, ht2⟩
    rw [div_lt_iff₀ hden] at ht1
    nlinarith [sq_nonneg (v t 2)]
  refine ⟨?_, hTle⟩
  intro t ht
  have hD : 0 < v 0 2 ^ 2 - 2 * γ * c0 * t := by
    have h1 : t < v 0 2 ^ 2 / (2 * γ * c0) := lt_of_lt_of_le ht.2 (htb ▸ hTle)
    rw [lt_div_iff₀ hden] at h1
    linarith
  have hnz : ∀ s ∈ Set.Ico 0 T, s ≤ t → v s 2 ≠ 0 := by
    intro s hs hst h
    have := hsq s hs
    rw [h] at this
    nlinarith [mul_le_mul_of_nonneg_left hst hden.le]
  have hvt : v t 2 ≠ 0 := hnz t ht le_rfl
  have hv0 : v 0 2 ≠ 0 := hnz 0 ⟨le_rfl, lt_of_le_of_lt ht.1 ht.2⟩ ht.1
  have hsub : Set.Icc 0 t ⊆ Set.Ico 0 T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hcIcc : ContinuousOn (fun s => v s 2) (Set.Icc 0 t) := (hcomp 2).mono hsub
  -- sign is preserved
  have hsign : Real.sign (v t 2) = Real.sign (v 0 2) := by
    rcases lt_or_gt_of_ne hv0 with h0 | h0 <;> rcases lt_or_gt_of_ne hvt with h1 | h1
    · rw [Real.sign_of_neg h0, Real.sign_of_neg h1]
    · exfalso
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 hcIcc ⟨h0.le, h1.le⟩
      exact hnz s (hsub hs) hs.2 hs0
    · exfalso
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 hcIcc ⟨h1.le, h0.le⟩
      exact hnz s (hsub hs) hs.2 hs0
    · rw [Real.sign_of_pos h0, Real.sign_of_pos h1]
  rw [← hsign, ← hsq t ht, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hvt with h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [Real.sign_of_pos h, abs_of_pos h]; ring
