-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:18:45.133992+00:00
-- url     : https://prove2.me/submissions/fbdb9660-a4b9-4a83-965d-1572954c45b7

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

theorem solution {𝒳 : Type*} [Fintype 𝒳] (p : 𝒳 → ℝ) (hp : IsPMF p) :
    ∃ C ≥ (0 : ℝ), ∀ α ∈ Set.Icc (1 / 2 : ℝ) 2, α ≠ 1 →
      |renyi α p - (shannon p - d1 p * (α - 1))| ≤ C * (α - 1) ^ 2 := by
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hlb : ∀ x, Real.logb 2 x = Real.log x / L := fun x => rfl
  set A := ∑ t, p t * Real.log (p t) with hA
  set B := ∑ t, p t * Real.log (p t) ^ 2 with hB
  have hlogS := BGEX_log (BGE34_S_expand p hp)
  obtain ⟨δ, hδ, C, hC, hexp⟩ := hlogS
  obtain ⟨KS, hKS, hKSb⟩ := BGE34_logS_bound p hp
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  set K0 := KS / (δ' * L) + |A| / L + |B - A ^ 2| / (2 * L) with hK0
  refine ⟨max (C / L) (K0 / δ' ^ 2), le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro α hα hα1
  set ε := α - 1 with hε
  have hε0 : ε ≠ 0 := sub_ne_zero.mpr hα1
  have hεpos : 0 < |ε| := abs_pos.mpr hε0
  have hε1 : |ε| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
  have hαpos : 0 < α := by linarith [hα.1]
  -- express everything through `S(ε)`
  have hSeq : ∑ t, p t ^ α = BGE34_S p ε := by
    unfold BGE34_S
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show α = 1 + ε by rw [hε]; ring]
    exact BGE34_rpow _ _ (hp.1 t) (by linarith)
  have hS0 := BGE34_S_pos p hp ε
  have hrenyi : renyi α p = Real.log (BGE34_S p ε) / (L * (1 - α)) := by
    unfold renyi
    rw [hSeq, Real.logb_rpow_eq_mul_logb_of_pos hS0, hlb]
    have : (1 : ℝ) - α ≠ 0 := by intro h; apply hα1; linarith
    field_simp
  have hshannon : shannon p = -A / L := by
    unfold shannon
    rw [hA, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hlb]; ring
  have hd1 : d1 p = (B - A ^ 2) / (2 * L) := by
    unfold d1
    rw [hshannon]
    have hlog_e : Real.logb 2 (Real.exp 1) = 1 / L := by
      rw [hlb, Real.log_exp]
    rw [hlog_e]
    have : ∑ t, p t * Real.logb 2 (p t) ^ 2 = B / L ^ 2 := by
      rw [hB, Finset.sum_div]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hlb]; field_simp
    rw [this]
    field_simp
    try ring
  have hkey : renyi α p - (shannon p - d1 p * (α - 1)) =
      -(Real.log (BGE34_S p ε) - (0 + A * ε + (∑ t, p t * Real.log (p t) ^ 2 / 2 - A ^ 2 / 2) * ε ^ 2))
        / (ε * L) := by
    rw [hrenyi, hshannon, hd1, ← Finset.sum_div, ← hB]
    have : (1 : ℝ) - α = -ε := by rw [hε]; ring
    rw [this, ← hε]
    field_simp
    ring
  rw [hkey, abs_div, abs_neg, abs_mul, abs_of_pos hL0]
  rcases le_or_gt |ε| δ' with hsmall | hbig
  · -- local regime
    have h := hexp ε (le_trans hsmall (min_le_left _ _))
    calc |Real.log (BGE34_S p ε) - (0 + A * ε + (∑ t, p t * Real.log (p t) ^ 2 / 2 - A ^ 2 / 2) * ε ^ 2)|
          / (|ε| * L) ≤ C * |ε| ^ 3 / (|ε| * L) :=
          div_le_div_of_nonneg_right h (by positivity)
      _ = C / L * ε ^ 2 := by
          rw [← sq_abs ε]; field_simp
      _ ≤ max (C / L) (K0 / δ' ^ 2) * ε ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · -- global regime
    have hlog := hKSb ε hε1
    have hnum : |Real.log (BGE34_S p ε) - (0 + A * ε + (∑ t, p t * Real.log (p t) ^ 2 / 2 - A ^ 2 / 2) * ε ^ 2)|
        ≤ KS + |A| * |ε| + |B - A ^ 2| / 2 * |ε| ^ 2 := by
      have e : (∑ t, p t * Real.log (p t) ^ 2 / 2 - A ^ 2 / 2) = (B - A ^ 2) / 2 := by
        rw [← Finset.sum_div, ← hB]; ring
      rw [e]
      calc _ ≤ |Real.log (BGE34_S p ε)| + |A * ε| + |(B - A ^ 2) / 2 * ε ^ 2| := by
            have := abs_sub (Real.log (BGE34_S p ε)) (0 + A * ε + (B - A ^ 2) / 2 * ε ^ 2)
            have := abs_add_le (A * ε) ((B - A ^ 2) / 2 * ε ^ 2)
            simp only [zero_add] at *
            linarith
        _ = |Real.log (BGE34_S p ε)| + |A| * |ε| + |B - A ^ 2| / 2 * |ε| ^ 2 := by
            rw [abs_mul, abs_mul, abs_div, abs_pow, abs_two]
        _ ≤ _ := by linarith
    have hK0pos : 0 ≤ K0 := by positivity
    calc _ ≤ (KS + |A| * |ε| + |B - A ^ 2| / 2 * |ε| ^ 2) / (|ε| * L) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = KS / (|ε| * L) + |A| / L + |B - A ^ 2| * |ε| / (2 * L) := by
          field_simp
      _ ≤ KS / (δ' * L) + |A| / L + |B - A ^ 2| / (2 * L) := by
          have h1 : KS / (|ε| * L) ≤ KS / (δ' * L) :=
            div_le_div_of_nonneg_left hKS (by positivity)
              (mul_le_mul_of_nonneg_right hbig.le hL0.le)
          have h2 : |B - A ^ 2| * |ε| / (2 * L) ≤ |B - A ^ 2| / (2 * L) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith [abs_nonneg (B - A ^ 2)]
          linarith
      _ = K0 := by rw [hK0]
      _ = K0 / δ' ^ 2 * δ' ^ 2 := by field_simp
      _ ≤ K0 / δ' ^ 2 * ε ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← sq_abs ε]; exact pow_le_pow_left₀ hδ'0.le hbig.le 2
      _ ≤ max (C / L) (K0 / δ' ^ 2) * ε ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
