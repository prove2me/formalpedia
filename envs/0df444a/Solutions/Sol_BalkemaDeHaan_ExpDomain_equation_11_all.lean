-- Prove2me | solution 1 for BalkemaDeHaan.ExpDomain.equation_11_all
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:30:32.665628+00:00
-- url     : https://prove2.me/submissions/87bb3c63-c67e-4052-a663-eab17d1bb375

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains



namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory Topology

lemma tail_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Antitone (BalkemaDeHaan.LimitTypes.tail μ) := by
  intro x y hxy
  unfold BalkemaDeHaan.LimitTypes.tail
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.Ioi_subset_Ioi hxy))

lemma eventually_lt_of_antitone {R : ℝ → ℝ} (hR : Antitone R) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (p q : ℕ → ℝ) (α β : ℝ)
    (hp : Tendsto (fun n => c n * R (p n)) atTop (𝓝 α))
    (hq : Tendsto (fun n => c n * R (q n)) atTop (𝓝 β)) (hαβ : α < β) :
    ∀ᶠ n in atTop, q n < p n := by
  have h1 := hp.eventually (gt_mem_nhds (show α < (α + β) / 2 by linarith))
  have h2 := hq.eventually (lt_mem_nhds (show (α + β) / 2 < β by linarith))
  filter_upwards [h1, h2] with n hn1 hn2
  by_contra hcon
  push_neg at hcon
  have := mul_le_mul_of_nonneg_left (hR hcon) (hc n)
  linarith

/-- `n / (n / K) → K` for the natural-number quotient. -/
lemma tendsto_div_natDiv (K : ℕ) (hK : 0 < K) :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n / K : ℕ) : ℝ)) atTop (𝓝 (K : ℝ)) := by
  have hq : Tendsto (fun n : ℕ => n / K) atTop atTop := Nat.tendsto_div_const_atTop hK.ne'
  have hup : Tendsto (fun n : ℕ => (K : ℝ) + (K : ℝ) / ((n / K : ℕ) : ℝ)) atTop (𝓝 ((K : ℝ) + 0)) :=
    tendsto_const_nhds.add ((tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)).comp hq)
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop K] with n hn
    have hq1 : 1 ≤ n / K := (Nat.one_le_div_iff hK).2 hn
    have hqpos : (0 : ℝ) < ((n / K : ℕ) : ℝ) := by exact_mod_cast hq1
    rw [le_div_iff₀ hqpos]
    have : K * (n / K) ≤ n := Nat.mul_div_le n K
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop K] with n hn
    have hq1 : 1 ≤ n / K := (Nat.one_le_div_iff hK).2 hn
    have hqpos : (0 : ℝ) < ((n / K : ℕ) : ℝ) := by exact_mod_cast hq1
    rw [div_le_iff₀ hqpos]
    have e : ((K : ℝ) + K / ((n / K : ℕ) : ℝ)) * ((n / K : ℕ) : ℝ) = K * ((n / K : ℕ) : ℝ) + K := by
      field_simp
    rw [e]
    have h1 : n = K * (n / K) + n % K := (Nat.div_add_mod n K).symm
    have h2 : n % K < K := Nat.mod_lt n hK
    have h3 : (n : ℝ) = K * ((n / K : ℕ) : ℝ) + ((n % K : ℕ) : ℝ) := by exact_mod_cast h1
    have h4 : ((n % K : ℕ) : ℝ) ≤ K := by exact_mod_cast h2.le
    rw [h3]
    linarith

/-- Squeeze principle with multiplicative tolerance. -/
lemma tendsto_of_exp_squeeze (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ l u : ℕ → ℝ,
      Tendsto l atTop (𝓝 (c * Real.exp (-ε))) ∧ Tendsto u atTop (𝓝 (c * Real.exp ε)) ∧
      ∀ᶠ n in atTop, l n ≤ f n ∧ f n ≤ u n) :
    Tendsto f atTop (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : ContinuousAt (fun ε : ℝ => c * Real.exp (-ε)) 0 := by fun_prop
    have h0 : a < c * Real.exp (-0) := by simpa using ha
    have hev := hcont.eventually (lt_mem_nhds h0)
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < c * Real.exp (-ε) ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num))
    obtain ⟨ε, hε, hε0, hε1⟩ := hev2.exists
    obtain ⟨l, u, hl, hu, hlu⟩ := h ε hε0 hε1
    filter_upwards [hl.eventually (lt_mem_nhds hε), hlu] with n hn hn2
    linarith [hn2.1]
  · intro a ha
    have hcont : ContinuousAt (fun ε : ℝ => c * Real.exp ε) 0 := by fun_prop
    have h0 : c * Real.exp 0 < a := by simpa using ha
    have hev := hcont.eventually (gt_mem_nhds h0)
    have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * Real.exp ε < a ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT (by norm_num))
    obtain ⟨ε, hε, hε0, hε1⟩ := hev2.exists
    obtain ⟨l, u, hl, hu, hlu⟩ := h ε hε0 hε1
    filter_upwards [hu.eventually (gt_mem_nhds hε), hlu] with n hn hn2
    linarith [hn2.2]

theorem equation_11_all_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : TailScaledConvergence μ a b (Set.Ioi 0)) :
    TailScaledConvergence μ a b Set.univ := by
  intro x₀ _
  rcases lt_or_ge 0 x₀ with hx | hx
  · exact h x₀ hx
  set R := BalkemaDeHaan.LimitTypes.tail μ with hRdef
  have hR : Antitone R := tail_antitone μ
  have hu : ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => (n : ℝ) * R (b n + x * a n)) atTop (𝓝 (Real.exp (-x))) :=
    fun x hx => h x hx
  -- choose K
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (1 - x₀))
  have hKpos : (0 : ℝ) < K := lt_trans (Real.exp_pos _) hK
  have hKnat : 0 < K := by exact_mod_cast hKpos
  set L := Real.log K with hL
  have hL1 : 1 - x₀ < L := by
    rw [hL]
    exact (Real.lt_log_iff_exp_lt hKpos).2 hK
  have hexpL : Real.exp L = K := Real.exp_log hKpos
  set m : ℕ → ℕ := fun n => n / K with hm
  have hm_top : Tendsto m atTop atTop := Nat.tendsto_div_const_atTop hKnat.ne'
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / ((m n : ℕ) : ℝ)) atTop (𝓝 (K : ℝ)) :=
    tendsto_div_natDiv K hKnat
  -- v_n(y) → K e^{-y}
  have hv : ∀ y : ℝ, 0 < y →
      Tendsto (fun n : ℕ => (n : ℝ) * R (b (m n) + y * a (m n))) atTop (𝓝 ((K : ℝ) * Real.exp (-y))) := by
    intro y hy
    have h1 := (hu y hy).comp hm_top
    have h2 := hratio.mul h1
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop K] with n hn
    have hq1 : 1 ≤ n / K := (Nat.one_le_div_iff hKnat).2 hn
    have hqpos : (0 : ℝ) < ((m n : ℕ) : ℝ) := by exact_mod_cast hq1
    simp only [Function.comp]
    field_simp
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ n := fun n => Nat.cast_nonneg n
  -- comparison: for x > 0, y > 0 with x > y - L, eventually b_m + y a_m < b_n + x a_n
  have cmp1 : ∀ x y : ℝ, 0 < x → 0 < y → y - L < x →
      ∀ᶠ n in atTop, b (m n) + y * a (m n) < b n + x * a n := by
    intro x y hx hy hxy
    refine eventually_lt_of_antitone hR (fun n => (n : ℝ)) hn0 _ _ _ _ (hu x hx) (hv y hy) ?_
    rw [← hexpL, ← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  have cmp2 : ∀ x y : ℝ, 0 < x → 0 < y → x < y - L →
      ∀ᶠ n in atTop, b n + x * a n < b (m n) + y * a (m n) := by
    intro x y hx hy hxy
    refine eventually_lt_of_antitone hR (fun n => (n : ℝ)) hn0 _ _ _ _ (hv y hy) (hu x hx) ?_
    rw [← hexpL, ← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  -- main squeeze
  set s := 1 - x₀ with hs
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  set y₀ := x₀ + L with hy₀
  have hy₀1 : 1 < y₀ := by rw [hy₀]; linarith
  have hlim : ∀ ε' : ℝ, (K : ℝ) * Real.exp (-(y₀ + ε')) = Real.exp (-x₀) * Real.exp (-ε') := by
    intro ε'
    rw [← hexpL, ← Real.exp_add, ← Real.exp_add, hy₀]
    congr 1
    ring
  refine tendsto_of_exp_squeeze _ _ (Real.exp_pos _) ?_
  intro ε' hε'0 hε'1
  set ε := ε' / (1 + 2 * s) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεlt : ε < 1 := by
    rw [hε, div_lt_one (by positivity)]
    linarith
  have hε' : ε' = ε * (1 + 2 * s) := by rw [hε]; field_simp
  refine ⟨fun n => (n : ℝ) * R (b (m n) + (y₀ + ε') * a (m n)),
    fun n => (n : ℝ) * R (b (m n) + (y₀ - ε') * a (m n)), ?_, ?_, ?_⟩
  · rw [← hlim]
    exact hv _ (by linarith)
  · have := hv (y₀ - ε') (by linarith)
    rw [show y₀ - ε' = y₀ + (-ε') by ring, hlim, neg_neg] at this
    exact this
  · have c1 := cmp1 1 (1 + L - ε) one_pos (by linarith) (by linarith)
    have c2 := cmp2 1 (1 + L + ε) one_pos (by linarith) (by linarith)
    have c3 := cmp2 2 (2 + L + ε) two_pos (by linarith) (by linarith)
    have c4 := cmp1 2 (2 + L - ε) two_pos (by linarith) (by linarith)
    filter_upwards [c1, c2, c3, c4] with n h1 h2 h3 h4
    have ham := ha (m n)
    have han := ha n
    have hspos : 0 < s := by linarith
    -- a_n < (1 + 2ε) a_m and a_n > (1 - 2ε) a_m
    have hA1 : a n < (1 + 2 * ε) * a (m n) := by linarith
    have hA2 : (1 - 2 * ε) * a (m n) < a n := by linarith
    have hA1' := mul_lt_mul_of_pos_left hA1 hspos
    have hA2' := mul_lt_mul_of_pos_left hA2 hspos
    have hx₀ : x₀ = 1 - s := by rw [hs]; ring
    have hP1 : b (m n) + (y₀ - ε') * a (m n) < b n + x₀ * a n := by
      rw [hx₀, hε', hy₀, hs]
      nlinarith
    have hP2 : b n + x₀ * a n < b (m n) + (y₀ + ε') * a (m n) := by
      rw [hx₀, hε', hy₀, hs]
      nlinarith
    constructor
    · exact mul_le_mul_of_nonneg_left (hR hP2.le) (hn0 n)
    · exact mul_le_mul_of_nonneg_left (hR hP1.le) (hn0 n)

end BalkemaDeHaan.ExpDomain

open BalkemaDeHaan.ExpDomain
open MeasureTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : TailScaledConvergence μ a b (Set.Ioi 0)) :
    TailScaledConvergence μ a b Set.univ := by
  exact equation_11_all_core μ a b ha h
