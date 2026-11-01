-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_5_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:22:23.450295+00:00
-- url     : https://prove2.me/submissions/b189219c-82fb-4ca8-b00f-dfd95487e7c4

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof


/-! A small calculus of second-order expansions with cubic remainder near `ε = 0`. -/

/-- `f ε = a0 + a1 ε + a2 ε² + O(|ε|³)` on a neighbourhood of `0`. -/
def BGEX (f : ℝ → ℝ) (a0 a1 a2 : ℝ) : Prop :=
  ∃ δ > 0, ∃ C ≥ 0, ∀ ε, |ε| ≤ δ → |f ε - (a0 + a1 * ε + a2 * ε ^ 2)| ≤ C * |ε| ^ 3

theorem BGEX_const (c : ℝ) : BGEX (fun _ => c) c 0 0 :=
  ⟨1, one_pos, 0, le_rfl, fun ε _ => by simp⟩

theorem BGEX_lin (c : ℝ) : BGEX (fun ε => c * ε) 0 c 0 :=
  ⟨1, one_pos, 0, le_rfl, fun ε _ => by simp⟩

theorem BGEX_add {f g : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : BGEX f a0 a1 a2)
    (hg : BGEX g b0 b1 b2) : BGEX (fun ε => f ε + g ε) (a0 + b0) (a1 + b1) (a2 + b2) := by
  obtain ⟨δf, hδf, Cf, hCf, hf⟩ := hf
  obtain ⟨δg, hδg, Cg, hCg, hg⟩ := hg
  refine ⟨min δf δg, lt_min hδf hδg, Cf + Cg, by positivity, fun ε hε => ?_⟩
  have h1 := hf ε (le_trans hε (min_le_left _ _))
  have h2 := hg ε (le_trans hε (min_le_right _ _))
  calc |f ε + g ε - (a0 + b0 + (a1 + b1) * ε + (a2 + b2) * ε ^ 2)|
      = |(f ε - (a0 + a1 * ε + a2 * ε ^ 2)) + (g ε - (b0 + b1 * ε + b2 * ε ^ 2))| := by ring_nf
    _ ≤ |f ε - (a0 + a1 * ε + a2 * ε ^ 2)| + |g ε - (b0 + b1 * ε + b2 * ε ^ 2)| := abs_add_le _ _
    _ ≤ Cf * |ε| ^ 3 + Cg * |ε| ^ 3 := add_le_add h1 h2
    _ = (Cf + Cg) * |ε| ^ 3 := by ring

theorem BGEX_smul {f : ℝ → ℝ} {a0 a1 a2 : ℝ} (c : ℝ) (hf : BGEX f a0 a1 a2) :
    BGEX (fun ε => c * f ε) (c * a0) (c * a1) (c * a2) := by
  obtain ⟨δ, hδ, C, hC, hf⟩ := hf
  refine ⟨δ, hδ, |c| * C, by positivity, fun ε hε => ?_⟩
  calc |c * f ε - (c * a0 + c * a1 * ε + c * a2 * ε ^ 2)|
      = |c| * |f ε - (a0 + a1 * ε + a2 * ε ^ 2)| := by rw [← abs_mul]; ring_nf
    _ ≤ |c| * (C * |ε| ^ 3) := mul_le_mul_of_nonneg_left (hf ε hε) (abs_nonneg _)
    _ = |c| * C * |ε| ^ 3 := by ring

theorem BGEX_congr {f g : ℝ → ℝ} {a0 a1 a2 : ℝ} (hf : BGEX f a0 a1 a2) (δ0 : ℝ) (hδ0 : 0 < δ0)
    (h : ∀ ε, |ε| ≤ δ0 → f ε = g ε) : BGEX g a0 a1 a2 := by
  obtain ⟨δ, hδ, C, hC, hf⟩ := hf
  refine ⟨min δ δ0, lt_min hδ hδ0, C, hC, fun ε hε => ?_⟩
  rw [← h ε (le_trans hε (min_le_right _ _))]
  exact hf ε (le_trans hε (min_le_left _ _))

theorem BGEX_coef_eq {f : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : BGEX f a0 a1 a2)
    (h0 : a0 = b0) (h1 : a1 = b1) (h2 : a2 = b2) : BGEX f b0 b1 b2 := by
  subst h0 h1 h2; exact hf

theorem BGEX_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a0 a1 a2 : ι → ℝ)
    (hf : ∀ i ∈ s, BGEX (f i) (a0 i) (a1 i) (a2 i)) :
    BGEX (fun ε => ∑ i ∈ s, f i ε) (∑ i ∈ s, a0 i) (∑ i ∈ s, a1 i) (∑ i ∈ s, a2 i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BGEX_const 0
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact BGEX_add (hf j (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- values are bounded near 0 -/
theorem BGEX_bound {f : ℝ → ℝ} {a0 a1 a2 : ℝ} (hf : BGEX f a0 a1 a2) :
    ∃ δ > 0, ∃ K ≥ 0, δ ≤ 1 ∧ ∀ ε, |ε| ≤ δ →
      |f ε - (a0 + a1 * ε + a2 * ε ^ 2)| ≤ K * |ε| ^ 3 ∧ |f ε - a0| ≤ K * |ε| := by
  obtain ⟨δ, hδ, C, hC, hf⟩ := hf
  refine ⟨min δ 1, lt_min hδ one_pos, C + |a1| + |a2|, by positivity, min_le_right _ _,
    fun ε hε => ?_⟩
  have hε1 : |ε| ≤ 1 := le_trans hε (min_le_right _ _)
  have h := hf ε (le_trans hε (min_le_left _ _))
  have he0 : 0 ≤ |ε| := abs_nonneg _
  have h3 : |ε| ^ 3 ≤ |ε| := by nlinarith [pow_le_pow_left₀ he0 hε1 2]
  have h2 : |ε| ^ 2 ≤ |ε| := by nlinarith
  constructor
  · calc |f ε - (a0 + a1 * ε + a2 * ε ^ 2)| ≤ C * |ε| ^ 3 := h
      _ ≤ (C + |a1| + |a2|) * |ε| ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity); linarith [abs_nonneg a1, abs_nonneg a2]
  · calc |f ε - a0| = |(f ε - (a0 + a1 * ε + a2 * ε ^ 2)) + a1 * ε + a2 * ε ^ 2| := by ring_nf
      _ ≤ |f ε - (a0 + a1 * ε + a2 * ε ^ 2)| + |a1 * ε| + |a2 * ε ^ 2| := abs_add_three _ _ _
      _ ≤ C * |ε| + |a1| * |ε| + |a2| * |ε| := by
          rw [abs_mul, abs_mul, abs_pow]
          have : C * |ε| ^ 3 ≤ C * |ε| := mul_le_mul_of_nonneg_left h3 hC
          have : |a2| * |ε| ^ 2 ≤ |a2| * |ε| := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          linarith
      _ = (C + |a1| + |a2|) * |ε| := by ring

theorem BGEX_mul {f g : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : BGEX f a0 a1 a2)
    (hg : BGEX g b0 b1 b2) :
    BGEX (fun ε => f ε * g ε) (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0) := by
  obtain ⟨δf, hδf, Kf, hKf, hδf1, hf⟩ := BGEX_bound hf
  obtain ⟨δg, hδg, Kg, hKg, hδg1, hg⟩ := BGEX_bound hg
  refine ⟨min δf δg, lt_min hδf hδg,
    Kf * (|b0| + |b1| + |b2|) + (|a0| + |a1| + |a2|) * Kg + Kf * Kg + |a1 * b2| + |a2 * b1|
      + |a2 * b2|, by positivity, fun ε hε => ?_⟩
  have hεf : |ε| ≤ δf := le_trans hε (min_le_left _ _)
  have hεg : |ε| ≤ δg := le_trans hε (min_le_right _ _)
  have hε1 : |ε| ≤ 1 := le_trans hεf hδf1
  obtain ⟨hf3, -⟩ := hf ε hεf
  obtain ⟨hg3, -⟩ := hg ε hεg
  set Rf := f ε - (a0 + a1 * ε + a2 * ε ^ 2)
  set Rg := g ε - (b0 + b1 * ε + b2 * ε ^ 2)
  set e := |ε| with he
  have he0 : 0 ≤ e := abs_nonneg _
  have he3 : e ^ 3 ≤ 1 := pow_le_one₀ he0 hε1
  have hPa : |a0 + a1 * ε + a2 * ε ^ 2| ≤ |a0| + |a1| + |a2| := by
    refine le_trans (abs_add_three _ _ _) ?_
    rw [abs_mul, abs_mul, abs_pow]
    have : |a1| * e ≤ |a1| := by nlinarith [abs_nonneg a1]
    have : |a2| * e ^ 2 ≤ |a2| := by nlinarith [abs_nonneg a2, pow_le_one₀ he0 hε1 (n := 2)]
    linarith
  have hPb : |b0 + b1 * ε + b2 * ε ^ 2| ≤ |b0| + |b1| + |b2| := by
    refine le_trans (abs_add_three _ _ _) ?_
    rw [abs_mul, abs_mul, abs_pow]
    have : |b1| * e ≤ |b1| := by nlinarith [abs_nonneg b1]
    have : |b2| * e ^ 2 ≤ |b2| := by nlinarith [abs_nonneg b2, pow_le_one₀ he0 hε1 (n := 2)]
    linarith
  have hfg : f ε * g ε - (a0 * b0 + (a0 * b1 + a1 * b0) * ε + (a0 * b2 + a1 * b1 + a2 * b0) * ε ^ 2)
      = Rf * (b0 + b1 * ε + b2 * ε ^ 2) + (a0 + a1 * ε + a2 * ε ^ 2) * Rg + Rf * Rg
        + (a1 * b2) * ε ^ 3 + (a2 * b1) * ε ^ 3 + (a2 * b2) * ε ^ 4 := by
    simp only [Rf, Rg]; ring
  rw [hfg]
  have t1 : |Rf * (b0 + b1 * ε + b2 * ε ^ 2)| ≤ Kf * (|b0| + |b1| + |b2|) * e ^ 3 := by
    rw [abs_mul]
    calc |Rf| * |b0 + b1 * ε + b2 * ε ^ 2| ≤ (Kf * e ^ 3) * (|b0| + |b1| + |b2|) :=
          mul_le_mul hf3 hPb (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t2 : |(a0 + a1 * ε + a2 * ε ^ 2) * Rg| ≤ (|a0| + |a1| + |a2|) * Kg * e ^ 3 := by
    rw [abs_mul]
    calc |a0 + a1 * ε + a2 * ε ^ 2| * |Rg| ≤ (|a0| + |a1| + |a2|) * (Kg * e ^ 3) :=
          mul_le_mul hPa hg3 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have t3 : |Rf * Rg| ≤ Kf * Kg * e ^ 3 := by
    rw [abs_mul]
    have hRf1 : |Rf| ≤ Kf := le_trans hf3 (by nlinarith)
    calc |Rf| * |Rg| ≤ Kf * (Kg * e ^ 3) := mul_le_mul hRf1 hg3 (abs_nonneg _) hKf
      _ = _ := by ring
  have t4 : |(a1 * b2) * ε ^ 3| ≤ |a1 * b2| * e ^ 3 := by rw [abs_mul, abs_pow]
  have t5 : |(a2 * b1) * ε ^ 3| ≤ |a2 * b1| * e ^ 3 := by rw [abs_mul, abs_pow]
  have t6 : |(a2 * b2) * ε ^ 4| ≤ |a2 * b2| * e ^ 3 := by
    rw [abs_mul, abs_pow]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [← he]; nlinarith [pow_nonneg he0 3]
  have := abs_add_le (Rf * (b0 + b1 * ε + b2 * ε ^ 2) + (a0 + a1 * ε + a2 * ε ^ 2) * Rg + Rf * Rg
        + (a1 * b2) * ε ^ 3 + (a2 * b1) * ε ^ 3) ((a2 * b2) * ε ^ 4)
  have := abs_add_le (Rf * (b0 + b1 * ε + b2 * ε ^ 2) + (a0 + a1 * ε + a2 * ε ^ 2) * Rg + Rf * Rg
        + (a1 * b2) * ε ^ 3) ((a2 * b1) * ε ^ 3)
  have := abs_add_le (Rf * (b0 + b1 * ε + b2 * ε ^ 2) + (a0 + a1 * ε + a2 * ε ^ 2) * Rg + Rf * Rg)
        ((a1 * b2) * ε ^ 3)
  have := abs_add_le (Rf * (b0 + b1 * ε + b2 * ε ^ 2) + (a0 + a1 * ε + a2 * ε ^ 2) * Rg) (Rf * Rg)
  have := abs_add_le (Rf * (b0 + b1 * ε + b2 * ε ^ 2)) ((a0 + a1 * ε + a2 * ε ^ 2) * Rg)
  nlinarith

theorem BGEX_small {D : ℝ → ℝ} (g : ℝ → ℝ) {b0 b1 b2 : ℝ} (hg : BGEX g b0 b1 b2) (r c : ℝ)
    (hr : 0 < r) (hc : 0 ≤ c)
    (hD : ∀ ε, |g ε - b0| ≤ r → |D ε| ≤ c * |g ε - b0| ^ 3) : BGEX D 0 0 0 := by
  obtain ⟨δ, hδ, K, hK, hδ1, hg⟩ := BGEX_bound hg
  refine ⟨min δ (r / (K + 1)), lt_min hδ (by positivity), c * K ^ 3, by positivity,
    fun ε hε => ?_⟩
  have hεδ : |ε| ≤ δ := le_trans hε (min_le_left _ _)
  obtain ⟨-, h1⟩ := hg ε hεδ
  have hεr : |ε| ≤ r / (K + 1) := le_trans hε (min_le_right _ _)
  have hgr : |g ε - b0| ≤ r := by
    have : K * |ε| ≤ r := by
      rw [le_div_iff₀ (by positivity)] at hεr
      nlinarith [abs_nonneg ε]
    linarith
  have := hD ε hgr
  simp only [zero_add, zero_mul, sub_zero]
  calc |D ε| ≤ c * |g ε - b0| ^ 3 := this
    _ ≤ c * (K * |ε|) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact pow_le_pow_left₀ (abs_nonneg _) h1 3
    _ = c * K ^ 3 * |ε| ^ 3 := by ring

theorem BGEX_exp {g : ℝ → ℝ} {b1 b2 : ℝ} (hg : BGEX g 0 b1 b2) :
    BGEX (fun ε => Real.exp (g ε)) 1 b1 (b2 + b1 ^ 2 / 2) := by
  have hsq := BGEX_mul hg hg
  have hP := BGEX_add (BGEX_add (BGEX_const 1) hg) (BGEX_smul (1 / 2) hsq)
  have hD : BGEX (fun ε => Real.exp (g ε) - (1 + g ε + 1 / 2 * (g ε * g ε))) 0 0 0 := by
    refine BGEX_small g hg 1 1 one_pos zero_le_one fun ε hε => ?_
    simp only [sub_zero] at hε ⊢
    have := Real.exp_bound hε (n := 3) (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial] at this
    calc |Real.exp (g ε) - (1 + g ε + 1 / 2 * (g ε * g ε))|
        = |Real.exp (g ε) - (1 + g ε + g ε ^ 2 / 2)| := by ring_nf
      _ ≤ |g ε| ^ 3 * (4 / 18) := by
          convert this using 2 <;> norm_num
      _ ≤ 1 * |g ε| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg (g ε)) 3]
  have := BGEX_add hP hD
  refine BGEX_coef_eq (BGEX_congr this 1 one_pos fun ε _ => by ring) (by ring) (by ring) (by ring)

theorem BGEX_log {g : ℝ → ℝ} {b1 b2 : ℝ} (hg : BGEX g 1 b1 b2) :
    BGEX (fun ε => Real.log (g ε)) 0 b1 (b2 - b1 ^ 2 / 2) := by
  have hv : BGEX (fun ε => g ε - 1) 0 b1 b2 :=
    BGEX_coef_eq (BGEX_add hg (BGEX_const (-1))) (by ring) (by ring) (by ring)
  have hsq := BGEX_mul hv hv
  have hQ := BGEX_add hv (BGEX_smul (-1 / 2) hsq)
  have hD : BGEX (fun ε => Real.log (g ε) - ((g ε - 1) + -1 / 2 * ((g ε - 1) * (g ε - 1)))) 0 0 0 := by
    refine BGEX_small g hg (1 / 2) 2 (by norm_num) (by norm_num) fun ε hε => ?_
    have hlt : |-(g ε - 1)| < 1 := by rw [abs_neg]; linarith
    have := Real.abs_log_sub_add_sum_range_le hlt 2
    simp [Finset.sum_range_succ] at this
    have h1 : 1 - |g ε - 1| ≥ 1 / 2 := by linarith
    have h2 : |g ε - 1| ^ 3 / (1 - |g ε - 1|) ≤ 2 * |g ε - 1| ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg (abs_nonneg (g ε - 1)) 3]
    calc |Real.log (g ε) - ((g ε - 1) + -1 / 2 * ((g ε - 1) * (g ε - 1)))|
        = |-(g ε - 1) + (g ε - 1) ^ 2 / 2 + Real.log (g ε)| := by ring_nf
      _ ≤ |g ε - 1| ^ 3 / (1 - |g ε - 1|) := by
          convert this using 2 <;> first | rw [abs_sub_comm] | ring_nf
      _ ≤ 2 * |g ε - 1| ^ 3 := h2
  have := BGEX_add hQ hD
  refine BGEX_coef_eq (BGEX_congr this 1 one_pos fun ε _ => by ring) (by ring) (by ring) (by ring)


open BoundedEntropyGames.ConvRate

/-- `S(ε) = ∑ p(x)^{1+ε}` written with exponentials. -/
noncomputable def BGE34_S {T : Type*} [Fintype T] (p : T → ℝ) (ε : ℝ) : ℝ :=
  ∑ t, p t * Real.exp (Real.log (p t) * ε)

theorem BGE34_rpow (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < 1 + ε) :
    a ^ (1 + ε) = a * Real.exp (Real.log a * ε) := by
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hε.ne']; simp
  · rw [Real.rpow_def_of_pos hpos, mul_add, mul_one, Real.exp_add, Real.exp_log hpos]

theorem BGE34_S_expand {T : Type*} [Fintype T] (p : T → ℝ) (hp : IsPMF p) :
    BGEX (BGE34_S p) 1 (∑ t, p t * Real.log (p t)) (∑ t, p t * Real.log (p t) ^ 2 / 2) := by
  have h := BGEX_sum Finset.univ (fun t ε => p t * Real.exp (Real.log (p t) * ε))
    (fun t => p t * 1) (fun t => p t * Real.log (p t))
    (fun t => p t * (0 + Real.log (p t) ^ 2 / 2))
    (fun t _ => BGEX_smul (p t) (BGEX_exp (BGEX_lin (Real.log (p t)))))
  refine BGEX_coef_eq h ?_ ?_ ?_
  · simp [hp.2]
  · rfl
  · refine Finset.sum_congr rfl fun t _ => by ring

theorem BGE34_S_pos {T : Type*} [Fintype T] (p : T → ℝ) (hp : IsPMF p) (ε : ℝ) :
    0 < BGE34_S p ε := by
  obtain ⟨t0, ht0⟩ : ∃ t, 0 < p t := by
    by_contra h
    push Not at h
    have : ∑ t, p t ≤ 0 := Finset.sum_nonpos fun t _ => h t
    linarith [hp.2]
  unfold BGE34_S
  exact lt_of_lt_of_le (mul_pos ht0 (Real.exp_pos _))
    (Finset.single_le_sum (f := fun t => p t * Real.exp (Real.log (p t) * ε))
      (fun t _ => mul_nonneg (hp.1 t) (Real.exp_pos _).le) (Finset.mem_univ t0))

/-- a uniform bound on `|log S(ε)|` for `|ε| ≤ 1` -/
theorem BGE34_logS_bound {T : Type*} [Fintype T] (p : T → ℝ) (hp : IsPMF p) :
    ∃ K ≥ 0, ∀ ε, |ε| ≤ 1 → |Real.log (BGE34_S p ε)| ≤ K := by
  obtain ⟨t0, ht0⟩ : ∃ t, 0 < p t := by
    by_contra h
    push Not at h
    have : ∑ t, p t ≤ 0 := Finset.sum_nonpos fun t _ => h t
    linarith [hp.2]
  set Smax := ∑ t, Real.exp (|Real.log (p t)|)
  set Smin := p t0 * Real.exp (-|Real.log (p t0)|)
  have hSmin : 0 < Smin := mul_pos ht0 (Real.exp_pos _)
  refine ⟨Smax + 1 / Smin, by positivity, fun ε hε => ?_⟩
  have hp1 : ∀ t, p t ≤ 1 := fun t => by
    rw [← hp.2]; exact Finset.single_le_sum (f := p) (fun t _ => hp.1 t) (Finset.mem_univ t)
  have hexp : ∀ t, |Real.log (p t) * ε| ≤ |Real.log (p t)| := fun t => by
    rw [abs_mul]; nlinarith [abs_nonneg (Real.log (p t))]
  have hup : BGE34_S p ε ≤ Smax := by
    unfold BGE34_S
    refine Finset.sum_le_sum fun t _ => ?_
    calc p t * Real.exp (Real.log (p t) * ε) ≤ 1 * Real.exp (|Real.log (p t)|) :=
          mul_le_mul (hp1 t) (Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hexp t)))
            (Real.exp_pos _).le zero_le_one
      _ = _ := one_mul _
  have hlow : Smin ≤ BGE34_S p ε := by
    unfold BGE34_S
    refine le_trans ?_ (Finset.single_le_sum (f := fun t => p t * Real.exp (Real.log (p t) * ε))
      (fun t _ => mul_nonneg (hp.1 t) (Real.exp_pos _).le) (Finset.mem_univ t0))
    apply mul_le_mul_of_nonneg_left _ (hp.1 t0)
    apply Real.exp_le_exp.mpr
    have := hexp t0
    rw [abs_le] at this
    linarith
  have hS := BGE34_S_pos p hp ε
  rw [abs_le]
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hS
    have : (BGE34_S p ε)⁻¹ ≤ 1 / Smin := by
      rw [one_div]; exact inv_anti₀ hSmin hlow
    have : 0 ≤ Smax := by positivity
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hS
    have : 0 ≤ 1 / Smin := by positivity
    linarith



open BoundedEntropyGames.ConvRate

theorem BGEX_inv1 : BGEX (fun ε => 1 / (1 + ε)) 1 (-1) 1 := by
  have hpoly := BGEX_add (BGEX_add (BGEX_const 1) (BGEX_lin (-1))) (BGEX_mul (BGEX_lin 1) (BGEX_lin 1))
  have hD : BGEX (fun ε => 1 / (1 + ε) - (1 + -1 * ε + 1 * ε * (1 * ε))) 0 0 0 := by
    refine BGEX_small (fun ε => 1 * ε) (BGEX_lin 1) (1 / 2) 2 (by norm_num) (by norm_num)
      fun ε hε => ?_
    simp only [one_mul, sub_zero] at hε ⊢
    have h1 : 1 / 2 ≤ 1 + ε := by rw [abs_le] at hε; linarith
    have e : 1 / (1 + ε) - (1 + -1 * ε + ε * ε) = -ε ^ 3 / (1 + ε) := by
      field_simp; ring
    rw [e, abs_div, abs_neg, abs_pow, abs_of_pos (by linarith : (0 : ℝ) < 1 + ε),
      div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (abs_nonneg ε) 3]
  have := BGEX_add hpoly hD
  exact BGEX_coef_eq (BGEX_congr this 1 one_pos fun ε _ => by ring) (by ring) (by ring) (by ring)

theorem BGE56_condPMF_pmf {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) (y : 𝒴) (hy : 0 < marginalY pXY y) : IsPMF (condPMF pXY y) := by
  refine ⟨fun x => div_nonneg (hp.1 _) hy.le, ?_⟩
  unfold condPMF
  rw [← Finset.sum_div]
  exact div_self hy.ne'

theorem BGE56_zero_of_marg {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) (y : 𝒴) (hy : marginalY pXY y = 0) (x : 𝒳) : pXY (x, y) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp.1 (x, y))).mp hy x (Finset.mem_univ x)

theorem solution {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    ∃ C ≥ (0 : ℝ), ∀ α ∈ Set.Icc (1 / 2 : ℝ) 2, α ≠ 1 →
      |condRenyi α pXY - (condEntropy pXY - condD1 pXY * (α - 1))| ≤ C * (α - 1) ^ 2 := by
  classical
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hlb : ∀ x, Real.logb 2 x = Real.log x / L := fun x => rfl
  set mY := marginalY pXY with hmY
  have hmY0 : ∀ y, 0 ≤ mY y := fun y => Finset.sum_nonneg fun x _ => hp.1 _
  have hmY1 : ∑ y, mY y = 1 := by
    simp only [hmY, marginalY]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun x y => pXY (x, y))]
    exact hp.2
  set q := condPMF pXY with hq
  set Ay : 𝒴 → ℝ := fun y => ∑ x, q y x * Real.log (q y x) with hAy
  set By : 𝒴 → ℝ := fun y => ∑ x, q y x * Real.log (q y x) ^ 2 with hBy
  set Ab := ∑ y, mY y * Ay y with hAb
  set Bb := ∑ y, mY y * By y with hBb
  -- the per-`y` exponent `w_y(ε) = log S_y(ε) / (1 + ε)`
  set w : 𝒴 → ℝ → ℝ := fun y ε => Real.log (BGE34_S (q y) ε) * (1 / (1 + ε)) with hw
  set T : ℝ → ℝ := fun ε => ∑ y, mY y * Real.exp (w y ε) with hT
  have hwexp : ∀ y, 0 < mY y → BGEX (fun ε => mY y * Real.exp (w y ε)) (mY y * 1) (mY y * Ay y)
      (mY y * (By y / 2 - Ay y)) := by
    intro y hy
    have hlog := BGEX_log (BGE34_S_expand (q y) (BGE56_condPMF_pmf pXY hp y hy))
    have hm := BGEX_mul hlog BGEX_inv1
    have he := BGEX_exp (BGEX_coef_eq hm (by ring) rfl rfl)
    refine BGEX_coef_eq (BGEX_smul (mY y) he) rfl ?_ ?_
    · simp only [hAy]; ring
    · simp only [hAy, hBy]; congr 1
      have : (∑ t, q y t * Real.log (q y t) ^ 2 / 2) = (∑ t, q y t * Real.log (q y t) ^ 2) / 2 := by
        rw [Finset.sum_div]
      rw [this]; ring
  have hTexp : BGEX T 1 Ab (Bb / 2 - Ab) := by
    have h := BGEX_sum Finset.univ (fun y ε => mY y * Real.exp (w y ε)) (fun y => mY y * 1)
      (fun y => mY y * Ay y) (fun y => mY y * (By y / 2 - Ay y)) (fun y _ => by
        rcases (hmY0 y).eq_or_lt with h0 | hpos
        · rw [← h0]; simpa using BGEX_const 0
        · exact hwexp y hpos)
    refine BGEX_coef_eq h ?_ rfl ?_
    · simp [hmY1]
    · simp only [hBb, hAb, mul_sub, Finset.sum_sub_distrib, mul_div_assoc', ← Finset.sum_div]
  have hG : BGEX (fun ε => (1 + ε) * Real.log (T ε)) 0 Ab (Bb / 2 - Ab ^ 2 / 2) := by
    have h1 : BGEX (fun ε => 1 + ε) 1 1 0 :=
      BGEX_coef_eq (BGEX_congr (BGEX_add (BGEX_const 1) (BGEX_lin 1)) 1 one_pos
        fun ε _ => by ring) (by ring) (by ring) (by ring)
    have := BGEX_mul h1 (BGEX_log hTexp)
    exact BGEX_coef_eq this (by ring) (by ring) (by ring)
  obtain ⟨δ, hδ, C, hC, hexp⟩ := hG
  -- global bound on `log T`
  have hKy : ∀ y, ∃ K ≥ 0, 0 < mY y → ∀ ε, |ε| ≤ 1 → |Real.log (BGE34_S (q y) ε)| ≤ K := by
    intro y
    by_cases hy : 0 < mY y
    · obtain ⟨K, hK, hb⟩ := BGE34_logS_bound (q y) (BGE56_condPMF_pmf pXY hp y hy)
      exact ⟨K, hK, fun _ => hb⟩
    · exact ⟨0, le_rfl, fun h => absurd h hy⟩
  choose Ky hKy0 hKyb using hKy
  set K := ∑ y, Ky y with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun y _ => hKy0 y
  have hlogT : ∀ ε, |ε| ≤ 1 / 2 → |Real.log (T ε)| ≤ 2 * K := by
    intro ε hε
    have h1 : 1 / 2 ≤ 1 + ε := by rw [abs_le] at hε; linarith
    have hwb : ∀ y, 0 < mY y → |w y ε| ≤ 2 * K := by
      intro y hy
      simp only [hw]
      rw [abs_mul, abs_div, abs_one, abs_of_pos (by linarith : (0 : ℝ) < 1 + ε)]
      have hle : Ky y ≤ K := Finset.single_le_sum (f := Ky) (fun y _ => hKy0 y) (Finset.mem_univ y)
      have := hKyb y hy ε (by linarith [abs_nonneg ε])
      have h2 : 1 / (1 + ε) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      calc |Real.log (BGE34_S (q y) ε)| * (1 / (1 + ε)) ≤ K * 2 :=
            mul_le_mul (le_trans this hle) h2 (by positivity) hK0
        _ = 2 * K := by ring
    have hTlo : Real.exp (-(2 * K)) ≤ T ε := by
      calc Real.exp (-(2 * K)) = ∑ y, mY y * Real.exp (-(2 * K)) := by
            rw [← Finset.sum_mul, hmY1, one_mul]
        _ ≤ T ε := by
            refine Finset.sum_le_sum fun y _ => ?_
            rcases (hmY0 y).eq_or_lt with h0 | hpos
            · rw [← h0]; simp
            · apply mul_le_mul_of_nonneg_left _ (hmY0 y)
              apply Real.exp_le_exp.mpr
              have := hwb y hpos; rw [abs_le] at this; linarith
    have hThi : T ε ≤ Real.exp (2 * K) := by
      calc T ε ≤ ∑ y, mY y * Real.exp (2 * K) := by
            refine Finset.sum_le_sum fun y _ => ?_
            rcases (hmY0 y).eq_or_lt with h0 | hpos
            · rw [← h0]; simp
            · apply mul_le_mul_of_nonneg_left _ (hmY0 y)
              apply Real.exp_le_exp.mpr
              have := hwb y hpos; rw [abs_le] at this; linarith
        _ = Real.exp (2 * K) := by rw [← Finset.sum_mul, hmY1, one_mul]
    have hTpos : 0 < T ε := lt_of_lt_of_le (Real.exp_pos _) hTlo
    rw [abs_le]; constructor
    · have := Real.log_le_log (Real.exp_pos _) hTlo
      rw [Real.log_exp] at this; linarith
    · have := Real.log_le_log hTpos hThi
      rw [Real.log_exp] at this; linarith
  -- identification of the Lean definitions
  have hcondH : condEntropy pXY = -Ab / L := by
    unfold condEntropy
    rw [hAb, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hAy, Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases (hmY0 y).eq_or_lt with h0 | hpos
    · have := BGE56_zero_of_marg pXY hp y h0.symm x
      simp [this, ← h0]
    · simp only [hq, condPMF, hlb]
      rw [← hmY]
      field_simp
  have hshq : ∀ y, shannon (q y) = -Ay y / L := by
    intro y
    unfold shannon
    rw [hAy, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hlb]; ring
  have hlog_e : Real.logb 2 (Real.exp 1) = 1 / L := by rw [hlb, Real.log_exp]
  have hd1q : ∀ y, d1 (q y) = (By y - Ay y ^ 2) / (2 * L) := by
    intro y
    unfold d1
    rw [hshq, hlog_e]
    have : ∑ t, q y t * Real.logb 2 (q y t) ^ 2 = By y / L ^ 2 := by
      rw [hBy, Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hlb]; field_simp
    rw [this]
    field_simp
    try ring
  have hcondD1 : condD1 pXY = (Bb - Ab ^ 2) / (2 * L) := by
    unfold condD1
    rw [← hq, ← hmY, hlog_e, hcondH]
    simp_rw [hd1q, hshq]
    rw [hBb, hAb]
    have e1 : ∑ y, mY y * ((By y - Ay y ^ 2) / (2 * L)) =
        (∑ y, mY y * By y - ∑ y, mY y * Ay y ^ 2) / (2 * L) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => by ring
    have e2 : ∑ y, mY y * (-Ay y / L) ^ 2 = (∑ y, mY y * Ay y ^ 2) / L ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => by ring
    rw [e1, e2]
    field_simp
    ring
  -- the inner sum of `condRenyi` is `T(ε)`
  have hTeq : ∀ α : ℝ, 0 < α → ∑ y, marginalY pXY y *
      (∑ x, (pXY (x, y) / marginalY pXY y) ^ α) ^ (1 / α) = T (α - 1) := by
    intro α hα
    simp only [hT]
    refine Finset.sum_congr rfl fun y _ => ?_
    rcases (hmY0 y).eq_or_lt with h0 | hpos
    · rw [← hmY, ← h0]; simp
    · rw [← hmY]
      congr 1
      have hS : ∑ x, (pXY (x, y) / mY y) ^ α = BGE34_S (q y) (α - 1) := by
        unfold BGE34_S
        refine Finset.sum_congr rfl fun x _ => ?_
        have := BGE34_rpow (q y x) (α - 1) (div_nonneg (hp.1 _) hpos.le) (by linarith)
        rw [show 1 + (α - 1) = α by ring] at this
        rw [← this]
        rfl
      rw [hS, Real.rpow_def_of_pos (BGE34_S_pos (q y) (BGE56_condPMF_pmf pXY hp y hpos) _)]
      simp only [hw]
      congr 1
      rw [show 1 + (α - 1) = α by ring]
  -- the main estimate
  set δ' := min δ (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  set c2 := Bb / 2 - Ab ^ 2 / 2 with hc2
  set K0 := 4 * K / (δ' * L) + |Ab| / L + |c2| / L with hK0def
  refine ⟨max (C / L) (K0 / δ' ^ 2), le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro α hα hα1
  set ε := α - 1 with hε
  have hε0 : ε ≠ 0 := sub_ne_zero.mpr hα1
  have hεpos : 0 < |ε| := abs_pos.mpr hε0
  have hε1 : |ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
  have hαpos : 0 < α := by linarith [hα.1]
  have hkey : condRenyi α pXY - (condEntropy pXY - condD1 pXY * (α - 1)) =
      -((1 + ε) * Real.log (T ε) - (0 + Ab * ε + c2 * ε ^ 2)) / (ε * L) := by
    unfold condRenyi
    rw [hTeq α hαpos, hcondH, hcondD1, hlb]
    have : (1 : ℝ) - α = -ε := by rw [hε]; ring
    rw [this, show α = 1 + ε by rw [hε]; ring, hc2]
    have h1ε : (1 : ℝ) + ε - 1 = ε := by ring
    rw [h1ε]
    field_simp
    ring
  rw [hkey, abs_div, abs_neg, abs_mul, abs_of_pos hL0]
  rcases le_or_gt |ε| δ' with hsmall | hbig
  · have h := hexp ε (le_trans hsmall (min_le_left _ _))
    calc |(1 + ε) * Real.log (T ε) - (0 + Ab * ε + c2 * ε ^ 2)| / (|ε| * L)
          ≤ C * |ε| ^ 3 / (|ε| * L) := div_le_div_of_nonneg_right h (by positivity)
      _ = C / L * ε ^ 2 := by rw [← sq_abs ε]; field_simp
      _ ≤ max (C / L) (K0 / δ' ^ 2) * ε ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hε2 : |ε| ≤ 1 / 2 ∨ 1 / 2 < |ε| := le_or_gt _ _
    -- bound `|(1+ε) log T|` by `4K` (for |ε| ≤ 1/2) — for larger |ε| we use ε ≤ 1 and T's form
    have hGb : |(1 + ε) * Real.log (T ε)| ≤ 4 * K := by
      have hT' : |Real.log (T ε)| ≤ 2 * K := by
        rcases hε2 with h | h
        · exact hlogT ε h
        · -- here ε ∈ (1/2, 1]; reuse the bound with the explicit computation
          have hεp : 0 < ε := by
            rw [abs_le] at hε1
            by_contra hneg; push Not at hneg
            have : |ε| = -ε := abs_of_nonpos hneg
            have : -ε ≤ 1 / 2 := by linarith [hα.1]
            linarith
          have hwb : ∀ y, 0 < mY y → |w y ε| ≤ 2 * K := by
            intro y hy
            simp only [hw]
            rw [abs_mul, abs_div, abs_one, abs_of_pos (by linarith : (0 : ℝ) < 1 + ε)]
            have hle : Ky y ≤ K :=
              Finset.single_le_sum (f := Ky) (fun y _ => hKy0 y) (Finset.mem_univ y)
            have := hKyb y hy ε hε1
            have h2 : 1 / (1 + ε) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
            calc |Real.log (BGE34_S (q y) ε)| * (1 / (1 + ε)) ≤ K * 2 :=
                  mul_le_mul (le_trans this hle) h2 (by positivity) hK0
              _ = 2 * K := by ring
          have hTlo : Real.exp (-(2 * K)) ≤ T ε := by
            calc Real.exp (-(2 * K)) = ∑ y, mY y * Real.exp (-(2 * K)) := by
                  rw [← Finset.sum_mul, hmY1, one_mul]
              _ ≤ T ε := by
                  refine Finset.sum_le_sum fun y _ => ?_
                  rcases (hmY0 y).eq_or_lt with h0 | hpos
                  · rw [← h0]; simp
                  · apply mul_le_mul_of_nonneg_left _ (hmY0 y)
                    apply Real.exp_le_exp.mpr
                    have := hwb y hpos; rw [abs_le] at this; linarith
          have hThi : T ε ≤ Real.exp (2 * K) := by
            calc T ε ≤ ∑ y, mY y * Real.exp (2 * K) := by
                  refine Finset.sum_le_sum fun y _ => ?_
                  rcases (hmY0 y).eq_or_lt with h0 | hpos
                  · rw [← h0]; simp
                  · apply mul_le_mul_of_nonneg_left _ (hmY0 y)
                    apply Real.exp_le_exp.mpr
                    have := hwb y hpos; rw [abs_le] at this; linarith
              _ = Real.exp (2 * K) := by rw [← Finset.sum_mul, hmY1, one_mul]
          have hTpos : 0 < T ε := lt_of_lt_of_le (Real.exp_pos _) hTlo
          rw [abs_le]; constructor
          · have := Real.log_le_log (Real.exp_pos _) hTlo
            rw [Real.log_exp] at this; linarith
          · have := Real.log_le_log hTpos hThi
            rw [Real.log_exp] at this; linarith
      rw [abs_mul]
      have : |1 + ε| ≤ 2 := by rw [abs_le] at hε1 ⊢; constructor <;> linarith
      calc |1 + ε| * |Real.log (T ε)| ≤ 2 * (2 * K) :=
            mul_le_mul this hT' (abs_nonneg _) (by norm_num)
        _ = 4 * K := by ring
    have hnum : |(1 + ε) * Real.log (T ε) - (0 + Ab * ε + c2 * ε ^ 2)|
        ≤ 4 * K + |Ab| * |ε| + |c2| * |ε| ^ 2 := by
      have := abs_sub ((1 + ε) * Real.log (T ε)) (0 + Ab * ε + c2 * ε ^ 2)
      have h2 := abs_add_le (Ab * ε) (c2 * ε ^ 2)
      rw [zero_add] at this ⊢
      rw [abs_mul, abs_mul, abs_pow] at h2
      linarith
    have hK0pos : 0 ≤ K0 := by positivity
    calc _ ≤ (4 * K + |Ab| * |ε| + |c2| * |ε| ^ 2) / (|ε| * L) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 4 * K / (|ε| * L) + |Ab| / L + |c2| * |ε| / L := by field_simp
      _ ≤ 4 * K / (δ' * L) + |Ab| / L + |c2| / L := by
          have h1 : 4 * K / (|ε| * L) ≤ 4 * K / (δ' * L) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_right hbig.le hL0.le)
          have h2 : |c2| * |ε| / L ≤ |c2| / L := by
            apply div_le_div_of_nonneg_right _ hL0.le
            nlinarith [abs_nonneg c2]
          linarith
      _ = K0 := by rw [hK0def]
      _ = K0 / δ' ^ 2 * δ' ^ 2 := by field_simp
      _ ≤ K0 / δ' ^ 2 * ε ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← sq_abs ε]; exact pow_le_pow_left₀ hδ'0.le hbig.le 2
      _ ≤ max (C / L) (K0 / δ' ^ 2) * ε ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
