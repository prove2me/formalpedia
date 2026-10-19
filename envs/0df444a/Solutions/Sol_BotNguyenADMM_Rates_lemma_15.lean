-- Prove2me | solution 1 for BotNguyenADMM.Rates.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:56:47.484181+00:00
-- url     : https://prove2.me/submissions/d9f381b4-5a9d-4471-9ba6-fc7f36677710

import Mathlib
set_option autoImplicit false

open Filter

lemma l15_eventually_le (e : ℕ → ℝ) (he_lim : Tendsto e atTop (nhds 0)) (ε : ℝ) (hε : 0 < ε)
    (k₀ : ℕ) : ∃ K : ℕ, k₀ ≤ K ∧ ∀ k ≥ K, e k < ε := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 he_lim) ε hε
  refine ⟨max N k₀, le_max_right _ _, fun k hk => ?_⟩
  have := hN k (le_trans (le_max_left _ _) hk)
  rw [Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

lemma l15_part1 (e : ℕ → ℝ) (he_nonneg : ∀ k, 0 ≤ e k)
    (he_lim : Tendsto e atTop (nhds 0)) (k₀ l₀ : ℕ)
    (Ce θ : ℝ) (hCe : 0 < Ce) (hθ : θ = 0)
    (h71 : ∀ k ≥ k₀, Ce * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - l₀) - e k) :
    ∃ K : ℕ, ∀ k ≥ K, e k = 0 := by
  subst hθ
  obtain ⟨N, -, hN⟩ := l15_eventually_le e he_lim Ce hCe 0
  refine ⟨max N k₀ + l₀, fun k hk => ?_⟩
  by_contra hne
  have hk0 : k ≥ k₀ := by omega
  have h := h71 k hk0
  rw [if_neg hne] at h
  simp only [mul_zero, Real.rpow_zero, mul_one] at h
  have h2 : e (k - l₀) < Ce := hN _ (by omega)
  have := he_nonneg k
  linarith

lemma l15_part2 (e : ℕ → ℝ) (he_nonneg : ∀ k, 0 ≤ e k) (he_anti : Antitone e)
    (he_lim : Tendsto e atTop (nhds 0)) (k₀ l₀ : ℕ) (hl₀ : 1 ≤ l₀)
    (Ce θ : ℝ) (hCe : 0 < Ce) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (h71 : ∀ k ≥ k₀, Ce * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - l₀) - e k) :
    ∃ Ce0 : ℝ, 0 < Ce0 ∧ ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧
      ∀ k ≥ k₀, 0 ≤ e k ∧ e k ≤ Ce0 * Q ^ k := by
  obtain ⟨K1, hK1, hK1'⟩ := l15_eventually_le e he_lim 1 one_pos k₀
  have hr0 : 0 < (1 + Ce)⁻¹ := by positivity
  have hr1 : (1 + Ce)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hQ0 : 0 < ((1 + Ce)⁻¹) ^ ((l₀ : ℝ)⁻¹) := Real.rpow_pos_of_pos hr0 _
  have hQl : (((1 + Ce)⁻¹) ^ ((l₀ : ℝ)⁻¹)) ^ l₀ = (1 + Ce)⁻¹ :=
    Real.rpow_inv_natCast_pow hr0.le (by omega)
  generalize ((1 + Ce)⁻¹) ^ ((l₀ : ℝ)⁻¹) = Q at hQ0 hQl
  have hQ1 : Q < 1 := by
    by_contra h
    push_neg at h
    have : 1 ≤ Q ^ l₀ := one_le_pow₀ h
    linarith
  have step : ∀ k ≥ K1, e k ≤ (1 + Ce)⁻¹ * e (k - l₀) := by
    intro k hk
    have h := h71 k (le_trans hK1 hk)
    by_cases h0 : e k = 0
    · rw [h0]; exact mul_nonneg hr0.le (he_nonneg _)
    · rw [if_neg h0] at h
      have hpos : 0 < e k := lt_of_le_of_ne (he_nonneg k) (Ne.symm h0)
      have hle1 : e k ≤ 1 := (hK1' k hk).le
      have h4 : e k ^ (1:ℝ) ≤ e k ^ (2*θ) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by linarith)
      rw [Real.rpow_one] at h4
      have h3 : Ce * e k ≤ e (k - l₀) - e k :=
        le_trans (mul_le_mul_of_nonneg_left h4 hCe.le) h
      rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
      nlinarith
  have hA : 0 < (e 0 + 1) / Q ^ (K1 + l₀) :=
    div_pos (by linarith [he_nonneg 0]) (pow_pos hQ0 _)
  have key : ∀ k, e k ≤ (e 0 + 1) / Q ^ (K1 + l₀) * Q ^ k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < K1 + l₀
      · have h1 : e k ≤ e 0 := he_anti (Nat.zero_le k)
        have h2 : Q ^ (K1 + l₀) ≤ Q ^ k := pow_le_pow_of_le_one hQ0.le hQ1.le hk.le
        have h3 : e 0 + 1 ≤ (e 0 + 1) / Q ^ (K1 + l₀) * Q ^ k := by
          calc e 0 + 1 = (e 0 + 1) / Q ^ (K1 + l₀) * Q ^ (K1 + l₀) := by
                field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 hA.le
        linarith
      · push_neg at hk
        have h1 := step k (by omega)
        have h2 := ih (k - l₀) (by omega)
        calc e k ≤ (1 + Ce)⁻¹ * e (k - l₀) := h1
          _ ≤ (1 + Ce)⁻¹ * ((e 0 + 1) / Q ^ (K1 + l₀) * Q ^ (k - l₀)) :=
              mul_le_mul_of_nonneg_left h2 hr0.le
          _ = (e 0 + 1) / Q ^ (K1 + l₀) * Q ^ k := by
              have : Q ^ k = Q ^ (k - l₀) * Q ^ l₀ := by
                rw [← pow_add]; congr 1; omega
              rw [this, hQl]; ring
  exact ⟨_, hA, Q, hQ0.le, hQ1, fun k _ => ⟨he_nonneg k, key k⟩⟩

lemma l15_part3 (e : ℕ → ℝ) (he_nonneg : ∀ k, 0 ≤ e k) (he_anti : Antitone e)
    (he_lim : Tendsto e atTop (nhds 0)) (k₀ l₀ : ℕ) (hl₀ : 1 ≤ l₀) (hkl : l₀ ≤ k₀)
    (Ce θ : ℝ) (hCe : 0 < Ce) (hθ0 : 1 / 2 < θ) (hθ1 : θ < 1)
    (h71 : ∀ k ≥ k₀, Ce * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - l₀) - e k) :
    ∃ Ce1 : ℝ, 0 < Ce1 ∧
      ∀ k ≥ k₀ + l₀, 0 ≤ e k ∧ e k ≤ Ce1 * ((k : ℝ) - l₀ + 1) ^ (-(1 / (2 * θ - 1))) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 2 * θ - 1 := ⟨_, rfl⟩
  rw [← hp]
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have h2θ : 2 * θ = 1 + p := by linarith
  have hl : (0 : ℝ) < l₀ := by exact_mod_cast hl₀
  obtain ⟨K1, hK1, hK1'⟩ := l15_eventually_le e he_lim 1 one_pos k₀
  have hρ0 : 0 < (1 / 2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : (1 / 2 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp0
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 / 2 : ℝ) ^ p := ⟨_, rfl⟩
  rw [← hρ] at hρ0 hρ1
  have hc0 : 0 < min (p * Ce / 2) (1 - ρ) := lt_min (by positivity) (by linarith)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (p * Ce / 2) (1 - ρ) := ⟨_, rfl⟩
  rw [← hc] at hc0
  have hc1 : c ≤ p * Ce / 2 := hc ▸ min_le_left _ _
  have hc2 : c ≤ 1 - ρ := hc ▸ min_le_right _ _
  -- one step
  have step : ∀ k ≥ K1, 0 < e k → (e (k - l₀) ^ p)⁻¹ + c ≤ (e k ^ p)⁻¹ := by
    intro k hk hx
    have h := h71 k (le_trans hK1 hk)
    rw [if_neg hx.ne', h2θ, Real.rpow_add hx, Real.rpow_one] at h
    have hxy : e k ≤ e (k - l₀) := he_anti (Nat.sub_le _ _)
    have hy : 0 < e (k - l₀) := lt_of_lt_of_le hx hxy
    have hx1 : e k ≤ 1 := (hK1' k hk).le
    have hz : 0 < e k ^ p := Real.rpow_pos_of_pos hx _
    have hw : 0 < e (k - l₀) ^ p := Real.rpow_pos_of_pos hy _
    have hz1 : e k ^ p ≤ 1 := Real.rpow_le_one hx.le hx1 hp0.le
    by_cases hcase : e (k - l₀) ≤ 2 * e k
    · -- Bernoulli step
      have hs : -1 ≤ e k / e (k - l₀) - 1 := by
        have : 0 ≤ e k / e (k - l₀) := by positivity
        linarith
      have hb := rpow_one_add_le_one_add_mul_self hs hp0.le hp1.le
      rw [add_sub_cancel, Real.div_rpow hx.le hy.le] at hb
      rw [div_le_iff₀ hw] at hb
      have ht : 1 / 2 ≤ e k / e (k - l₀) := by
        rw [div_le_div_iff₀ (by norm_num) hy]; linarith
      have h5 : Ce * e k * e k ^ p / e (k - l₀) ≤ (e (k - l₀) - e k) / e (k - l₀) :=
        div_le_div_of_nonneg_right (by linarith [h, mul_assoc Ce (e k) (e k ^ p)]) hy.le
      have h6 : Ce * e k * e k ^ p / e (k - l₀) = Ce * e k ^ p * (e k / e (k - l₀)) := by
        ring
      have h7 : (e (k - l₀) - e k) / e (k - l₀) = 1 - e k / e (k - l₀) := by
        field_simp
      have h8 : Ce * e k ^ p / 2 ≤ 1 - e k / e (k - l₀) := by
        have : Ce * e k ^ p / 2 ≤ Ce * e k ^ p * (e k / e (k - l₀)) := by
          have : 0 ≤ Ce * e k ^ p := by positivity
          nlinarith
        linarith
      -- w - z ≥ w p (1 - t)
      have h9 : e (k - l₀) ^ p * (p * Ce * e k ^ p / 2) ≤ e (k - l₀) ^ p - e k ^ p := by
        have : 0 ≤ e (k - l₀) ^ p * p := by positivity
        nlinarith
      have h10 : (e k ^ p)⁻¹ - (e (k - l₀) ^ p)⁻¹
          = (e (k - l₀) ^ p - e k ^ p) / (e k ^ p * e (k - l₀) ^ p) := by
        field_simp
      have h11 : p * Ce / 2 ≤ (e k ^ p)⁻¹ - (e (k - l₀) ^ p)⁻¹ := by
        rw [h10, le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    · push_neg at hcase
      have h1 : e k ^ p ≤ ρ * e (k - l₀) ^ p := by
        rw [hρ, ← Real.mul_rpow (by norm_num) hy.le]
        exact Real.rpow_le_rpow hx.le (by linarith) hp0.le
      have h2 : e k ^ p / e (k - l₀) ^ p ≤ ρ := by
        rw [div_le_iff₀ hw]; linarith
      have h3 : (e (k - l₀) ^ p)⁻¹ ≤ ρ * (e k ^ p)⁻¹ := by
        calc (e (k - l₀) ^ p)⁻¹ = (e k ^ p / e (k - l₀) ^ p) * (e k ^ p)⁻¹ := by
              field_simp
          _ ≤ ρ * (e k ^ p)⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hz.le)
      have h4 : 1 ≤ (e k ^ p)⁻¹ := one_le_inv₀ hz |>.2 hz1
      nlinarith
  have key : ∀ k ≥ K1, 0 < e k → c / l₀ * ((k : ℝ) - K1 + 1) ≤ (e k ^ p)⁻¹ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hpos
      have hz : 0 < e k ^ p := Real.rpow_pos_of_pos hpos _
      have hz1 : 1 ≤ (e k ^ p)⁻¹ :=
        (one_le_inv₀ hz).2 (Real.rpow_le_one hpos.le (hK1' k hk).le hp0.le)
      by_cases hk2 : k < K1 + l₀
      · have h1 : (k : ℝ) - K1 + 1 ≤ l₀ := by
          have : (k : ℝ) + 1 ≤ K1 + l₀ := by exact_mod_cast hk2
          linarith
        calc c / l₀ * ((k : ℝ) - K1 + 1) ≤ c / l₀ * l₀ :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = c := by field_simp
          _ ≤ 1 := by linarith
          _ ≤ _ := hz1
      · push_neg at hk2
        have hpos' : 0 < e (k - l₀) := lt_of_lt_of_le hpos (he_anti (Nat.sub_le _ _))
        have h1 := step k hk hpos
        have h2 := ih (k - l₀) (by omega) (by omega) hpos'
        have hcast : ((k - l₀ : ℕ) : ℝ) = (k : ℝ) - l₀ := by
          rw [Nat.cast_sub (by omega)]
        rw [hcast] at h2
        have h3 : c / l₀ * ((k : ℝ) - K1 + 1) = c / l₀ * ((k : ℝ) - l₀ - K1 + 1) + c := by
          field_simp; ring
        linarith
  -- lower bound for small indices
  have hb0 : 0 < ((e 0 + 1) ^ p)⁻¹ := by
    have : 0 < e 0 + 1 := by linarith [he_nonneg 0]
    positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((e 0 + 1) ^ p)⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hb0
  have hbk : ∀ k, 0 < e k → b ≤ (e k ^ p)⁻¹ := by
    intro k hk
    have hz : 0 < e k ^ p := Real.rpow_pos_of_pos hk _
    have h1 : e k ^ p ≤ (e 0 + 1) ^ p :=
      Real.rpow_le_rpow hk.le (by linarith [he_anti (Nat.zero_le k)]) hp0.le
    rw [hb]
    exact inv_anti₀ hz h1
  have hm : (0 : ℝ) < (K1 : ℝ) + 1 := by positivity
  have hcl : 0 < c / l₀ := by positivity
  have hcc : 0 < min (c / l₀ / ((K1 : ℝ) + 1)) (b / ((K1 : ℝ) + 1)) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min (c / l₀ / ((K1 : ℝ) + 1)) (b / ((K1 : ℝ) + 1)) :=
    ⟨_, rfl⟩
  rw [← hd] at hcc
  have hd1 : d * ((K1 : ℝ) + 1) ≤ c / l₀ := by
    have : d ≤ c / l₀ / ((K1 : ℝ) + 1) := hd ▸ min_le_left _ _
    rwa [le_div_iff₀ hm] at this
  have hd2 : d * ((K1 : ℝ) + 1) ≤ b := by
    have : d ≤ b / ((K1 : ℝ) + 1) := hd ▸ min_le_right _ _
    rwa [le_div_iff₀ hm] at this
  have main : ∀ k ≥ k₀ + l₀, 0 < e k → d * ((k : ℝ) - l₀ + 1) ≤ (e k ^ p)⁻¹ := by
    intro k hk hpos
    by_cases hkK : K1 ≤ k
    · have h1 := key k hkK hpos
      have ha : (1 : ℝ) ≤ (k : ℝ) - K1 + 1 := by
        have : (K1 : ℝ) ≤ k := by exact_mod_cast hkK
        linarith
      have hK0 : (0 : ℝ) ≤ K1 := Nat.cast_nonneg _
      have hlk : (0 : ℝ) ≤ l₀ := hl.le
      have h2 : (k : ℝ) - l₀ + 1 ≤ ((K1 : ℝ) + 1) * ((k : ℝ) - K1 + 1) := by nlinarith
      calc d * ((k : ℝ) - l₀ + 1) ≤ d * (((K1 : ℝ) + 1) * ((k : ℝ) - K1 + 1)) :=
            mul_le_mul_of_nonneg_left h2 hcc.le
        _ = (d * ((K1 : ℝ) + 1)) * ((k : ℝ) - K1 + 1) := by ring
        _ ≤ (c / l₀) * ((k : ℝ) - K1 + 1) := mul_le_mul_of_nonneg_right hd1 (by linarith)
        _ ≤ _ := h1
    · push_neg at hkK
      have h1 : (k : ℝ) - l₀ + 1 ≤ (K1 : ℝ) + 1 := by
        have : (k : ℝ) ≤ K1 := by exact_mod_cast hkK.le
        have : (0 : ℝ) ≤ l₀ := hl.le
        linarith
      calc d * ((k : ℝ) - l₀ + 1) ≤ d * ((K1 : ℝ) + 1) := mul_le_mul_of_nonneg_left h1 hcc.le
        _ ≤ b := hd2
        _ ≤ _ := hbk k hpos
  refine ⟨(d⁻¹) ^ (p⁻¹), Real.rpow_pos_of_pos (inv_pos.2 hcc) _, fun k hk => ⟨he_nonneg k, ?_⟩⟩
  have hX : (0 : ℝ) < (k : ℝ) - l₀ + 1 := by
    have : (l₀ : ℝ) ≤ k := by exact_mod_cast (by omega : l₀ ≤ k)
    linarith
  rcases (he_nonneg k).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have hz : 0 < e k ^ p := Real.rpow_pos_of_pos hpos _
    have h1 := main k hk hpos
    have h2 : e k ^ p ≤ (d * ((k : ℝ) - l₀ + 1))⁻¹ := by
      have := inv_anti₀ (by positivity) h1
      rwa [inv_inv] at this
    have h3 : (e k ^ p) ^ p⁻¹ ≤ ((d * ((k : ℝ) - l₀ + 1))⁻¹) ^ p⁻¹ :=
      Real.rpow_le_rpow hz.le h2 (inv_nonneg.2 hp0.le)
    rw [Real.rpow_rpow_inv hpos.le hp0.ne'] at h3
    rw [one_div, Real.rpow_neg hX.le, ← Real.inv_rpow hX.le, mul_comm]
    calc e k ≤ _ := h3
      _ = _ := by
        rw [mul_inv, Real.mul_rpow (inv_nonneg.2 hcc.le) (inv_nonneg.2 hX.le), mul_comm]

theorem solution (e : ℕ → ℝ) (he_nonneg : ∀ k, 0 ≤ e k) (he_anti : Antitone e)
    (he_lim : Filter.Tendsto e Filter.atTop (nhds 0)) (k₀ l₀ : ℕ) (hl₀ : 1 ≤ l₀) (hkl : l₀ ≤ k₀)
    (Ce θ : ℝ) (hCe : 0 < Ce) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h71 : ∀ k ≥ k₀, Ce * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - l₀) - e k) :
    (θ = 0 → ∃ K : ℕ, ∀ k ≥ K, e k = 0) ∧
    (0 < θ ∧ θ ≤ 1 / 2 → ∃ Ce0 : ℝ, 0 < Ce0 ∧ ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧
      ∀ k ≥ k₀, 0 ≤ e k ∧ e k ≤ Ce0 * Q ^ k) ∧
    (1 / 2 < θ ∧ θ < 1 → ∃ Ce1 : ℝ, 0 < Ce1 ∧
      ∀ k ≥ k₀ + l₀, 0 ≤ e k ∧ e k ≤ Ce1 * ((k : ℝ) - l₀ + 1) ^ (-(1 / (2 * θ - 1)))) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact l15_part1 e he_nonneg he_lim k₀ l₀ Ce θ hCe h h71
  · exact l15_part2 e he_nonneg he_anti he_lim k₀ l₀ hl₀ Ce θ hCe h.1 h.2 h71
  · exact l15_part3 e he_nonneg he_anti he_lim k₀ l₀ hl₀ hkl Ce θ hCe h.1 h.2 h71
