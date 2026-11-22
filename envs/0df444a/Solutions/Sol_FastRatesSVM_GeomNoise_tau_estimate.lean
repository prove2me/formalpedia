-- Prove2me | solution 1 for FastRatesSVM.GeomNoise.tau_estimate
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T09:28:49.465535+00:00
-- url     : https://prove2.me/submissions/d4f6dfaf-9379-417d-b979-d5cdbffd48bb

import Mathlib

theorem solution (γ q cγ : ℝ) (hγ : 0 < γ) (hq : 0 ≤ q) (hcγ : 0 < cγ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (∃ τ : ℝ, 0 < τ ∧ τ ^ (q + 1) = Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹)) ∧
      ∀ τ : ℝ, 0 < τ → τ ^ (q + 1) = Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹) →
        τ ≤ (cγ ^ (2 / γ) * (q + 1) * γ / 2) ^ (γ / 2) *
          (t * Real.log (1 / (cγ ^ (2 / γ) * (q + 1) * t))) ^ (γ / 2) := by
  have hq1 : 0 < q + 1 := by linarith
  set A : ℝ := (q + 1) * γ / 2 with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set C : ℝ := cγ ^ (2 / γ) with hC
  have hCpos : 0 < C := by rw [hC]; exact Real.rpow_pos_of_pos hcγ _
  set B : ℝ → ℝ := fun t => Real.log (1 / (C * (q + 1) * t)) with hB
  set t₀ : ℝ := (C * (q + 1))⁻¹ * Real.exp (-((q + 1) / A + 1)) with ht0
  refine ⟨t₀, ?_, ?_⟩
  · -- positivity of t₀
    rw [ht0]
    positivity
  · intro t ht ht0lt
    have hCt_pos : 0 < C * (q + 1) := mul_pos hCpos hq1
    -- Step 1: A * B t > q + 1 and B t > 0
    have hBt_gt : (q + 1) / A + 1 < B t := by
      have h1 : C * (q + 1) * t < Real.exp (-((q + 1) / A + 1)) := by
        have h2 : C * (q + 1) * t < C * (q + 1) * t₀ := by nlinarith
        have h3 : C * (q + 1) * t₀ = Real.exp (-((q + 1) / A + 1)) := by
          rw [ht0]
          field_simp
        linarith
      have h2 : Real.exp ((q + 1) / A + 1) * (C * (q + 1) * t) < 1 := by
        calc Real.exp ((q + 1) / A + 1) * (C * (q + 1) * t)
            < Real.exp ((q + 1) / A + 1) * Real.exp (-((q + 1) / A + 1)) :=
              mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
          _ = 1 := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h3 : Real.exp ((q + 1) / A + 1) < 1 / (C * (q + 1) * t) := by
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have h4 : Real.log (Real.exp ((q + 1) / A + 1)) < Real.log (1 / (C * (q + 1) * t)) :=
        Real.log_lt_log (Real.exp_pos _) h3
      rw [Real.log_exp] at h4
      exact h4
    have hBpos : 0 < B t := by
      have h1 : 0 < (q + 1) / A + 1 := by positivity
      linarith
    have hAB_gt : q + 1 < A * B t := by
      have h1 : A * ((q + 1) / A + 1) < A * B t := by
        exact mul_lt_mul_of_pos_left hBt_gt hApos
      have h2 : A * ((q + 1) / A + 1) = q + 1 + A := by
        field_simp
      rw [h2] at h1
      linarith
    -- Existence via IVT for g τ = τ^(q+1) - exp(-(τ/cγ)^(2/γ) * t⁻¹)
    have hexists : ∃ τ : ℝ, 0 < τ ∧ τ ^ (q + 1) = Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹) := by
      let g : ℝ → ℝ := fun τ => τ ^ (q + 1) - Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹)
      have hcont : ContinuousOn g (Set.Icc (0 : ℝ) 2) := by
        apply ContinuousOn.sub
        · exact (Real.continuous_rpow_const (le_of_lt hq1)).continuousOn
        · apply Real.continuous_exp.comp_continuousOn
          apply ContinuousOn.mul
          · apply ContinuousOn.neg
            apply ContinuousOn.rpow_const
            · exact continuousOn_id.div_const cγ
            · intro x hx
              right
              positivity
          · exact continuous_const.continuousOn
      have hg0 : g 0 = -1 := by
        simp only [g]
        rw [Real.zero_rpow hq1.ne']
        have h2 : (0 / cγ) ^ (2 / γ) = 0 := by
          rw [zero_div]
          exact Real.zero_rpow (by positivity : (2 : ℝ) / γ ≠ 0)
        rw [h2]
        norm_num
      have hg2 : 0 < g 2 := by
        have h1 : Real.exp (-(2 / cγ) ^ (2 / γ) * t⁻¹) ≤ 1 := by
          have h2 : 0 ≤ (2 / cγ) ^ (2 / γ) * t⁻¹ := by positivity
          exact Real.exp_le_one_iff.mpr (by linarith)
        have h2 : 1 < (2 : ℝ) ^ (q + 1) := Real.one_lt_rpow (by norm_num) hq1
        simp only [g]
        linarith
      have hivt : (0 : ℝ) ∈ g '' Set.Icc (0 : ℝ) 2 :=
        intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hcont (by
          rw [hg0]
          exact ⟨by linarith, le_of_lt hg2⟩)
      obtain ⟨τ, hτmem, hτg⟩ := hivt
      have hτpos : 0 < τ := by
        have h1 : τ ≠ 0 := by
          intro h0
          have h2 : g τ = -1 := by rw [h0]; exact hg0
          linarith
        exact lt_of_le_of_ne hτmem.1 (Ne.symm h1)
      have hτeq : τ ^ (q + 1) = Real.exp (-(τ / cγ) ^ (2 / γ) * t⁻¹) := by
        simp only [g] at hτg
        linarith
      exact ⟨τ, hτpos, hτeq⟩
    refine ⟨hexists, ?_⟩
    -- Step 2: any positive solution is bounded
    intro τ hτpos hτeq
    set s : ℝ := (τ / cγ) ^ (2 / γ) * t⁻¹ with hs
    have hs_pos : 0 < s := by
      rw [hs]
      have h1 : 0 < τ / cγ := div_pos hτpos hcγ
      have h2 : 0 < (τ / cγ) ^ (2 / γ) := Real.rpow_pos_of_pos h1 _
      exact mul_pos h2 (inv_pos.mpr ht)
    have hτ_eq : τ = cγ * (s * t) ^ (γ / 2) := by
      have h1 : (τ / cγ) ^ (2 / γ) = s * t := by
        rw [hs]
        field_simp
      calc τ = cγ * (τ / cγ) := by field_simp
        _ = cγ * ((τ / cγ) ^ (2 / γ)) ^ (γ / 2) := by
              rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ τ / cγ)]
              rw [show (2 / γ) * (γ / 2) = 1 by field_simp, Real.rpow_one]
        _ = cγ * (s * t) ^ (γ / 2) := by rw [h1]
    -- log identity
    have hlogτ : (q + 1) * Real.log τ = -s := by
      have h1 : Real.log (τ ^ (q + 1)) = Real.log (Real.exp (-s)) := by
        rw [hτeq, hs]
        congr 1
        ring
      rw [Real.log_rpow hτpos, Real.log_exp] at h1
      linarith
    have hkey : s + A * Real.log s = A * B t + A * Real.log (q + 1) := by
      have hlogC : Real.log C = (2 / γ) * Real.log cγ := by
        rw [hC, Real.log_rpow hcγ]
      have hBexp : B t = -Real.log C - Real.log (q + 1) - Real.log t := by
        rw [hB]
        simp only
        rw [Real.log_div one_ne_zero (by positivity : C * (q + 1) * t ≠ 0)]
        rw [show C * (q + 1) * t = C * ((q + 1) * t) by ring]
        rw [Real.log_mul hCpos.ne' (by positivity : (q + 1) * t ≠ 0)]
        rw [Real.log_mul hq1.ne' ht.ne', Real.log_one]
        ring
      have hlog_eq : Real.log τ = Real.log cγ + (γ / 2) * (Real.log s + Real.log t) := by
        rw [hτ_eq]
        rw [Real.log_mul hcγ.ne' (by positivity : (s * t) ^ (γ / 2) ≠ 0)]
        rw [Real.log_rpow (by positivity : 0 < s * t)]
        rw [Real.log_mul hs_pos.ne' ht.ne']
      have hs2 : s = -((q + 1) * Real.log cγ) - A * (Real.log s + Real.log t) := by
        have h1 : s = -((q + 1) * Real.log τ) := by linarith [hlogτ]
        nth_rewrite 1 [h1]
        rw [hlog_eq, hA]
        ring
      have hBval : A * B t + A * Real.log (q + 1) = -A * Real.log C - A * Real.log t := by
        rw [hBexp]
        ring
      have hAC : A * Real.log C = (q + 1) * Real.log cγ := by
        rw [hlogC, hA]
        field_simp
      linarith [hs2, hBval, hAC]
    -- Step 3: s < A * B t by strict monotonicity
    have hmono_f : ∀ x y : ℝ, 0 < x → x < y → x + A * Real.log x < y + A * Real.log y := by
      intro x y hx hxy
      have hy : 0 < y := lt_trans hx hxy
      have h1 : Real.log x < Real.log y := Real.log_lt_log hx hxy
      nlinarith
    have hs_lt : s < A * B t := by
      have hABpos : 0 < A * B t := by nlinarith [hAB_gt, hq1]
      have h1 : A * B t + A * Real.log (q + 1) < A * B t + A * Real.log (A * B t) := by
        have h2 : Real.log (q + 1) < Real.log (A * B t) := Real.log_lt_log hq1 hAB_gt
        nlinarith
      by_contra hnot
      push Not at hnot
      have h2 : A * B t + A * Real.log (A * B t) ≤ s + A * Real.log s := by
        rcases lt_or_eq_of_le hnot with h | h
        · exact le_of_lt (hmono_f (A * B t) s hABpos h)
        · rw [h]
      rw [← hkey] at h1
      linarith
    -- Step 4: conclude the bound
    have hτ_lt : τ < cγ * (A * B t * t) ^ (γ / 2) := by
      rw [hτ_eq]
      apply mul_lt_mul_of_pos_left _ hcγ
      apply Real.rpow_lt_rpow
      · positivity
      · nlinarith [hs_pos, ht]
      · positivity
    have hfinal : cγ * (A * B t * t) ^ (γ / 2) =
        (C * A) ^ (γ / 2) * (t * B t) ^ (γ / 2) := by
      have hcγ_eq : cγ = C ^ (γ / 2) := by
        rw [hC]
        rw [← Real.rpow_mul (le_of_lt hcγ)]
        rw [show (2 / γ) * (γ / 2) = 1 by field_simp, Real.rpow_one]
      calc cγ * (A * B t * t) ^ (γ / 2)
          = C ^ (γ / 2) * (A * B t * t) ^ (γ / 2) := by rw [hcγ_eq]
        _ = C ^ (γ / 2) * (A ^ (γ / 2) * (t * B t) ^ (γ / 2)) := by
              rw [show A * B t * t = A * (t * B t) by ring]
              rw [Real.mul_rpow (le_of_lt hApos) (by positivity : (0 : ℝ) ≤ t * B t)]
        _ = (C * A) ^ (γ / 2) * (t * B t) ^ (γ / 2) := by
              rw [Real.mul_rpow (le_of_lt hCpos) (le_of_lt hApos)]
              ring
    have hCA : C * A = cγ ^ (2 / γ) * (q + 1) * γ / 2 := by
      rw [hC, hA]
      ring
    calc τ ≤ cγ * (A * B t * t) ^ (γ / 2) := le_of_lt hτ_lt
      _ = (C * A) ^ (γ / 2) * (t * B t) ^ (γ / 2) := hfinal
      _ = (cγ ^ (2 / γ) * (q + 1) * γ / 2) ^ (γ / 2) *
            (t * Real.log (1 / (cγ ^ (2 / γ) * (q + 1) * t))) ^ (γ / 2) := by
            have hB' : B t = Real.log (1 / (cγ ^ (2 / γ) * (q + 1) * t)) := by
              rw [hB, hC]
            rw [hCA, hB']
