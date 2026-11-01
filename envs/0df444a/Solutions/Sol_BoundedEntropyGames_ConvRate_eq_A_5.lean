-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.eq_A_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:54:12.045264+00:00
-- url     : https://prove2.me/submissions/d750eaf6-24df-4934-a9ed-9875e0b697a8

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_A_11

open Complex Complex.HadamardThreeLines

/-- `‖s · exp(c · log a)‖ ≤ a ^ Re c` when `a ≥ 0`, `|s| ≤ 1`, and `s = 0` if `a = 0`. -/
theorem BGERT_norm_le (a s : ℝ) (c : ℂ) (ha : 0 ≤ a) (hs : |s| ≤ 1) (hs0 : a = 0 → s = 0) :
    ‖(s : ℂ) * cexp (c * (Real.log a : ℂ))‖ ≤ a ^ c.re := by
  rcases ha.eq_or_lt with h0 | hpos
  · rw [hs0 h0.symm]; simp only [Complex.ofReal_zero, zero_mul, norm_zero]
    exact Real.rpow_nonneg ha _
  · rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      Real.rpow_def_of_pos hpos]
    have : (c * (Real.log a : ℂ)).re = Real.log a * c.re := by
      simp [Complex.mul_re]; ring
    rw [this]
    calc |s| * Real.exp (Real.log a * c.re) ≤ 1 * Real.exp (Real.log a * c.re) :=
          mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
      _ = _ := one_mul _

/-- crude bound `‖s · exp(c · log a)‖ ≤ exp(|Re c| · |log a|)` -/
theorem BGERT_norm_le' (a s : ℝ) (c : ℂ) (hs : |s| ≤ 1) :
    ‖(s : ℂ) * cexp (c * (Real.log a : ℂ))‖ ≤ Real.exp (|c.re| * |Real.log a|) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have : (c * (Real.log a : ℂ)).re = c.re * Real.log a := by
    simp [Complex.mul_re]
  rw [this]
  calc |s| * Real.exp (c.re * Real.log a) ≤ 1 * Real.exp (|c.re| * |Real.log a|) := by
        apply mul_le_mul hs _ (Real.exp_pos _).le (by norm_num)
        apply Real.exp_le_exp.mpr
        rw [← abs_mul]; exact le_abs_self _
    _ = _ := one_mul _

theorem BGERT_sign_abs (v : ℝ) : abs (v / abs v) ≤ 1 := by
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr h)]

/-- Discrete Riesz–Thorin interpolation between `L¹ → L¹` and `L² → L²` bounds. -/
theorem BGERT_main {ι κ : Type*} [Fintype ι] [Fintype κ] (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (K : ι → κ → ℝ) (M0 M1sq : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1sq)
    (E1 : ∀ w : κ → ℂ, ∑ i, μ i * ‖∑ k, (K i k : ℂ) * w k‖ ≤ M0 * ∑ k, ‖w k‖)
    (E2 : ∀ w : κ → ℂ, ∑ i, μ i * ‖∑ k, (K i k : ℂ) * w k‖ ^ 2 ≤ M1sq * ∑ k, ‖w k‖ ^ 2)
    (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) 2) (g : κ → ℝ) :
    ∑ i, μ i * |∑ k, K i k * g k| ^ α ≤ M0 ^ (2 - α) * M1sq ^ (α - 1) * ∑ k, |g k| ^ α := by
  obtain ⟨hα1, hα2⟩ := hα
  have hαpos : 0 < α := by linarith
  set θ : ℝ := 2 - 2 / α with hθ
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_iff₀ hαpos]; linarith
  have hθ1 : θ ≤ 1 := by
    have : 1 ≤ 2 / α := by rw [le_div_iff₀ hαpos]; linarith
    linarith
  set a : κ → ℝ := fun k => |g k| with ha
  set s : κ → ℝ := fun k => g k / |g k| with hs
  set G : ι → ℝ := fun i => ∑ k, K i k * g k with hG
  set b : ι → ℝ := fun i => |G i| with hb
  set t : ι → ℝ := fun i => G i / |G i| with ht
  set Ng : ℝ := ∑ k, a k ^ α with hNg
  set A : ℝ := ∑ i, μ i * b i ^ α with hA
  have ha0 : ∀ k, 0 ≤ a k := fun k => abs_nonneg _
  have hb0 : ∀ i, 0 ≤ b i := fun i => abs_nonneg _
  have hs1 : ∀ k, |s k| ≤ 1 := fun k => BGERT_sign_abs _
  have ht1 : ∀ i, |t i| ≤ 1 := fun i => BGERT_sign_abs _
  have hs0 : ∀ k, a k = 0 → s k = 0 := fun k h => by simp [hs, ha] at h ⊢; simp [h]
  have ht0 : ∀ i, b i = 0 → t i = 0 := fun i h => by simp [ht, hb] at h ⊢; simp [h]
  have hNg0 : 0 ≤ Ng := Finset.sum_nonneg fun k _ => Real.rpow_nonneg (ha0 k) _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (Real.rpow_nonneg (hb0 i) _)
  -- analytic families
  let gz : ℂ → κ → ℂ := fun z k =>
    (s k : ℂ) * cexp (((α : ℂ) * (1 - z / 2)) * (Real.log (a k) : ℂ))
  let hz : ℂ → ι → ℂ := fun z i =>
    (t i : ℂ) * cexp (((α : ℂ) * z / 2) * (Real.log (b i) : ℂ))
  let Φ : ℂ → ℂ := fun z => ∑ i, (μ i : ℂ) * (∑ k, (K i k : ℂ) * gz z k) * hz z i
  -- differentiability
  have hdiff : Differentiable ℂ Φ := by
    simp only [Φ, gz, hz]
    fun_prop
  -- boundedness on the strip
  have hbdd : BddAbove ((norm ∘ Φ) '' verticalClosedStrip 0 1) := by
    refine ⟨∑ i, μ i * (∑ k, |K i k| * Real.exp (α * |Real.log (a k)|)) *
      Real.exp (α * |Real.log (b i)|), ?_⟩
    rintro _ ⟨z, hz', rfl⟩
    have hre : 0 ≤ z.re ∧ z.re ≤ 1 := hz'
    simp only [Function.comp, Φ]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
    apply mul_le_mul (mul_le_mul_of_nonneg_left _ (hμ i)) _ (norm_nonneg _)
      (mul_nonneg (hμ i) (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
        (Real.exp_pos _).le))
    · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine le_trans (BGERT_norm_le' _ _ _ (hs1 k)) (Real.exp_le_exp.mpr ?_)
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have : ((α : ℂ) * (1 - z / 2)).re = α * (1 - z.re / 2) := by
        simp [Complex.mul_re, Complex.sub_re]
      rw [this, abs_of_nonneg (by nlinarith)]
      nlinarith
    · refine le_trans (BGERT_norm_le' _ _ _ (ht1 i)) (Real.exp_le_exp.mpr ?_)
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have : ((α : ℂ) * z / 2).re = α * z.re / 2 := by
        simp [Complex.mul_re]
      rw [this, abs_of_nonneg (div_nonneg (mul_nonneg hαpos.le hre.1) (by norm_num))]
      nlinarith
  -- value at θ
  have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hαpos.ne'
  have hcθ : (α : ℂ) * (1 - (θ : ℂ) / 2) = 1 := by
    rw [hθ]; push_cast; field_simp; ring
  have hcθ' : (α : ℂ) * (θ : ℂ) / 2 = ((α - 1 : ℝ) : ℂ) := by
    rw [hθ]; push_cast; field_simp; try ring
  have hgθ : ∀ k, gz (θ : ℂ) k = (g k : ℂ) := by
    intro k
    simp only [gz]
    rw [hcθ, one_mul]
    rcases (ha0 k).eq_or_lt with h0 | hpos
    · rw [hs0 k h0.symm]
      have : g k = 0 := by simpa [ha] using h0.symm
      simp [this]
    · rw [← Complex.ofReal_exp, Real.exp_log hpos, ← Complex.ofReal_mul]
      congr 1
      simp only [hs, ha]
      exact div_mul_cancel₀ _ (ne_of_gt hpos)
  have hhθ : ∀ i, hz (θ : ℂ) i = ((t i * b i ^ (α - 1) : ℝ) : ℂ) := by
    intro i
    simp only [hz]
    rw [hcθ']
    rcases (hb0 i).eq_or_lt with h0 | hpos
    · rw [ht0 i h0.symm]; simp
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
        Real.rpow_def_of_pos hpos, mul_comm (α - 1)]
  have hGt : ∀ i, G i * t i * b i ^ (α - 1) = b i ^ α := by
    intro i
    have h1 : G i * t i = b i := by
      simp only [ht, hb]
      rcases eq_or_ne (G i) 0 with h | h
      · simp [h]
      · rw [mul_div_assoc', ← sq, ← sq_abs, sq, mul_div_assoc, div_self (abs_ne_zero.mpr h),
          mul_one]
    rw [h1, ← Real.rpow_one_add' (hb0 i) (by linarith)]
    congr 1; ring
  have hΦθ : Φ (θ : ℂ) = (A : ℂ) := by
    simp only [Φ, hgθ, hhθ, hA]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hGt i
    simp only [hG] at this
    rw [← this]
    push_cast
    ring
  -- edge Re z = 0
  have edge0 : ∀ z ∈ Complex.re ⁻¹' {0}, ‖Φ z‖ ≤ M0 * Ng := by
    intro z hz0
    have hre : z.re = 0 := hz0
    simp only [Φ]
    calc ‖∑ i, (μ i : ℂ) * (∑ k, (K i k : ℂ) * gz z k) * hz z i‖
        ≤ ∑ i, μ i * ‖∑ k, (K i k : ℂ) * gz z k‖ := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
          have : ‖hz z i‖ ≤ 1 := by
            refine le_trans (BGERT_norm_le _ _ _ (hb0 i) (ht1 i) (ht0 i)) ?_
            have : ((α : ℂ) * z / 2).re = 0 := by simp [Complex.mul_re, hre]
            rw [this, Real.rpow_zero]
          calc μ i * ‖∑ k, (K i k : ℂ) * gz z k‖ * ‖hz z i‖
              ≤ μ i * ‖∑ k, (K i k : ℂ) * gz z k‖ * 1 :=
                mul_le_mul_of_nonneg_left this (mul_nonneg (hμ i) (norm_nonneg _))
            _ = _ := mul_one _
      _ ≤ M0 * ∑ k, ‖gz z k‖ := E1 _
      _ ≤ M0 * Ng := by
          apply mul_le_mul_of_nonneg_left _ hM0
          refine Finset.sum_le_sum fun k _ => ?_
          refine le_trans (BGERT_norm_le _ _ _ (ha0 k) (hs1 k) (hs0 k)) (le_of_eq ?_)
          congr 1
          simp [Complex.mul_re, hre]
  -- edge Re z = 1
  have edge1 : ∀ z ∈ Complex.re ⁻¹' {1}, ‖Φ z‖ ≤ Real.sqrt (M1sq * Ng) * Real.sqrt A := by
    intro z hz1
    have hre : z.re = 1 := hz1
    have hgk : ∀ k, ‖gz z k‖ ^ 2 ≤ a k ^ α := by
      intro k
      have h1 := BGERT_norm_le _ _ ((α : ℂ) * (1 - z / 2)) (ha0 k) (hs1 k) (hs0 k)
      have : ((α : ℂ) * (1 - z / 2)).re = α / 2 := by
        simp [Complex.mul_re, hre]; ring
      rw [this] at h1
      calc ‖gz z k‖ ^ 2 ≤ (a k ^ (α / 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = a k ^ α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (ha0 k)]; norm_num
    have hhi : ∀ i, ‖hz z i‖ ^ 2 ≤ b i ^ α := by
      intro i
      have h1 := BGERT_norm_le _ _ ((α : ℂ) * z / 2) (hb0 i) (ht1 i) (ht0 i)
      have : ((α : ℂ) * z / 2).re = α / 2 := by
        simp [Complex.mul_re, hre]
      rw [this] at h1
      calc ‖hz z i‖ ^ 2 ≤ (b i ^ (α / 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = b i ^ α := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hb0 i)]; norm_num
    simp only [Φ]
    calc ‖∑ i, (μ i : ℂ) * (∑ k, (K i k : ℂ) * gz z k) * hz z i‖
        ≤ ∑ i, (Real.sqrt (μ i) * ‖∑ k, (K i k : ℂ) * gz z k‖) *
            (Real.sqrt (μ i) * ‖hz z i‖) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ i)]
          rw [show (Real.sqrt (μ i) * ‖∑ k, (K i k : ℂ) * gz z k‖) * (Real.sqrt (μ i) * ‖hz z i‖)
            = (Real.sqrt (μ i) * Real.sqrt (μ i)) * ‖∑ k, (K i k : ℂ) * gz z k‖ * ‖hz z i‖ by ring,
            Real.mul_self_sqrt (hμ i)]
      _ ≤ Real.sqrt (∑ i, (Real.sqrt (μ i) * ‖∑ k, (K i k : ℂ) * gz z k‖) ^ 2) *
            Real.sqrt (∑ i, (Real.sqrt (μ i) * ‖hz z i‖) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (M1sq * Ng) * Real.sqrt A := by
          apply mul_le_mul (Real.sqrt_le_sqrt _) (Real.sqrt_le_sqrt _) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
          · simp_rw [mul_pow, Real.sq_sqrt (hμ _)]
            refine le_trans (E2 _) (mul_le_mul_of_nonneg_left ?_ hM1)
            exact Finset.sum_le_sum fun k _ => hgk k
          · simp_rw [mul_pow, Real.sq_sqrt (hμ _)]
            exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hhi i) (hμ i)
  -- three lines
  have hθmem : (θ : ℂ) ∈ verticalClosedStrip 0 1 := by
    show (θ : ℂ).re ∈ Set.Icc (0 : ℝ) 1
    simp only [Complex.ofReal_re]; exact ⟨hθ0, hθ1⟩
  have h3 := norm_le_interp_of_mem_verticalClosedStrip₀₁' Φ hθmem hdiff.diffContOnCl hbdd
    edge0 edge1
  rw [hΦθ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0, Complex.ofReal_re] at h3
  -- final algebra
  show A ≤ M0 ^ (2 - α) * M1sq ^ (α - 1) * Ng
  have hRHS0 : 0 ≤ M0 ^ (2 - α) * M1sq ^ (α - 1) * Ng :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)) hNg0
  rcases hA0.eq_or_lt with hAz | hApos
  · rw [← hAz]; exact hRHS0
  set X := M1sq * Ng with hX
  have hX0 : 0 ≤ X := mul_nonneg hM1 hNg0
  set P := M0 * Ng with hP
  have hP0 : 0 ≤ P := mul_nonneg hM0 hNg0
  have hQ : (Real.sqrt X * Real.sqrt A) ^ θ = X ^ (θ / 2) * A ^ (θ / 2) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hX0 _)
      (Real.rpow_nonneg hA0 _), ← Real.rpow_mul hX0, ← Real.rpow_mul hA0]
    congr 2 <;> ring
  rw [hQ] at h3
  set R := P ^ (1 - θ) * X ^ (θ / 2) with hR
  have hR0 : 0 ≤ R := mul_nonneg (Real.rpow_nonneg hP0 _) (Real.rpow_nonneg hX0 _)
  have hsplit : A = A ^ (1 / α) * A ^ (θ / 2) := by
    rw [← Real.rpow_add hApos, show 1 / α + θ / 2 = 1 by rw [hθ]; field_simp; ring,
      Real.rpow_one]
  have hAθ : 0 < A ^ (θ / 2) := Real.rpow_pos_of_pos hApos _
  have h4 : A ^ (1 / α) ≤ R := by
    have : A ^ (1 / α) * A ^ (θ / 2) ≤ R * A ^ (θ / 2) := by
      rw [← hsplit]; rw [hR]; linarith [h3]
    exact le_of_mul_le_mul_right this hAθ
  have h5 : A ≤ R ^ α := by
    calc A = (A ^ (1 / α)) ^ α := by
          rw [← Real.rpow_mul hA0, one_div_mul_cancel hαpos.ne', Real.rpow_one]
      _ ≤ R ^ α := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) h4 hαpos.le
  have h6 : R ^ α = M0 ^ (2 - α) * M1sq ^ (α - 1) * Ng := by
    rw [hR, Real.mul_rpow (Real.rpow_nonneg hP0 _) (Real.rpow_nonneg hX0 _),
      ← Real.rpow_mul hP0, ← Real.rpow_mul hX0,
      show (1 - θ) * α = 2 - α by rw [hθ]; field_simp; try ring,
      show θ / 2 * α = α - 1 by rw [hθ]; field_simp; try ring,
      hP, hX, Real.mul_rpow hM0 hNg0, Real.mul_rpow hM1 hNg0]
    have : Ng ^ (2 - α) * Ng ^ (α - 1) = Ng := by
      rw [← Real.rpow_add' hNg0 (by ring_nf; norm_num)]
      ring_nf; exact Real.rpow_one _
    calc M0 ^ (2 - α) * Ng ^ (2 - α) * (M1sq ^ (α - 1) * Ng ^ (α - 1))
        = M0 ^ (2 - α) * M1sq ^ (α - 1) * (Ng ^ (2 - α) * Ng ^ (α - 1)) := by ring
      _ = _ := by rw [this]
  linarith [h5, h6]

open BoundedEntropyGames.ConvRate

theorem BGEA5_sum_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : ι → κ → ℝ) : ∑ f : ι → κ, ∏ i, w i (f i) = ∏ i, ∑ b, w i b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset κ)), Fintype.piFinset_univ]

/-- single-coordinate expectation under `p_F` -/
theorem BGEA5_expect1 {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) (x : 𝒳) (φ : 𝒜 → ℝ) :
    ∑ f : 𝒳 → 𝒜, pF pA f * φ (f x) = ∑ b, pA b * φ b := by
  have h1 : ∀ f : 𝒳 → 𝒜, pF pA f * φ (f x) =
      ∏ z, (pA (f z) * (if z = x then φ (f z) else 1)) := by
    intro f
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp [pF]
  simp_rw [h1]
  rw [BGEA5_sum_prod (fun z b => pA b * (if z = x then φ b else 1))]
  have : ∀ z, ∑ b, pA b * (if z = x then φ b else 1) = if z = x then ∑ b, pA b * φ b else 1 := by
    intro z
    by_cases hz : z = x
    · simp [hz]
    · simp [hz, hpA.2]
  simp_rw [this]
  rw [Finset.prod_ite_eq']
  simp

theorem solution {𝒳 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒜] [DecidableEq 𝒜]
    (pA : 𝒜 → ℝ) (hpA : IsPMF pA) :
    ∀ α ∈ Set.Icc (1 : ℝ) 2, ∀ (g : 𝒳 → ℝ) (a : 𝒜),
      ∑ f : 𝒳 → 𝒜, pF pA f * |∑ x, g x * ((if f x = a then 1 else 0) - pA a)| ^ α
        ≤ (2 : ℝ) ^ (2 - α) * pA a * ∑ x, |g x| ^ α := by
  intro α hα g a
  have hpa0 : 0 ≤ pA a := hpA.1 a
  have hpa1 : pA a ≤ 1 := by
    rw [← hpA.2]
    exact Finset.single_le_sum (f := pA) (fun b _ => hpA.1 b) (Finset.mem_univ a)
  set K : (𝒳 → 𝒜) → 𝒳 → ℝ := fun f x => (if f x = a then 1 else 0) - pA a with hK
  have habsK : ∀ b : 𝒜, |(if b = a then (1 : ℝ) else 0) - pA a| =
      (if b = a then 1 - 2 * pA a else 0) + pA a := by
    intro b
    by_cases hb : b = a
    · simp [hb, abs_of_nonneg (sub_nonneg.mpr hpa1)]; ring
    · simp [hb, abs_of_nonneg hpa0]
  have hE1x : ∀ x : 𝒳, ∑ f : 𝒳 → 𝒜, pF pA f * |K f x| ≤ 2 * pA a := by
    intro x
    have := BGEA5_expect1 pA hpA x (fun b => |(if b = a then (1 : ℝ) else 0) - pA a|)
    simp only [hK]
    rw [this]
    simp_rw [habsK, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← Finset.sum_mul, hpA.2]
    nlinarith
  have E1 : ∀ w : 𝒳 → ℂ, ∑ f : 𝒳 → 𝒜, pF pA f * ‖∑ x, (K f x : ℂ) * w x‖ ≤
      (2 * pA a) * ∑ x, ‖w x‖ := by
    intro w
    calc ∑ f : 𝒳 → 𝒜, pF pA f * ‖∑ x, (K f x : ℂ) * w x‖
        ≤ ∑ f : 𝒳 → 𝒜, pF pA f * ∑ x, |K f x| * ‖w x‖ := by
          refine Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left ?_
            (Finset.prod_nonneg fun _ _ => hpA.1 _)
          refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ = ∑ x, ‖w x‖ * ∑ f : 𝒳 → 𝒜, pF pA f * |K f x| := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun f _ => by ring
      _ ≤ ∑ x, ‖w x‖ * (2 * pA a) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hE1x x) (norm_nonneg _)
      _ = (2 * pA a) * ∑ x, ‖w x‖ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have E2 : ∀ w : 𝒳 → ℂ, ∑ f : 𝒳 → 𝒜, pF pA f * ‖∑ x, (K f x : ℂ) * w x‖ ^ 2 ≤
      pA a * ∑ x, ‖w x‖ ^ 2 := by
    intro w
    have hre := (eq_A_11 pA hpA (fun x => (w x).re) a).2
    have him := (eq_A_11 pA hpA (fun x => (w x).im) a).2
    have hsplit : ∀ f : 𝒳 → 𝒜, ‖∑ x, (K f x : ℂ) * w x‖ ^ 2 =
        |∑ x, (w x).re * ((if f x = a then 1 else 0) - pA a)| ^ 2 +
        |∑ x, (w x).im * ((if f x = a then 1 else 0) - pA a)| ^ 2 := by
      intro f
      have hre_eq : (∑ x, (K f x : ℂ) * w x).re =
          ∑ x, (w x).re * ((if f x = a then 1 else 0) - pA a) := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.re_ofReal_mul]; exact mul_comm _ _
      have him_eq : (∑ x, (K f x : ℂ) * w x).im =
          ∑ x, (w x).im * ((if f x = a then 1 else 0) - pA a) := by
        rw [Complex.im_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.im_ofReal_mul]; exact mul_comm _ _
      rw [Complex.sq_norm, Complex.normSq_apply, hre_eq, him_eq, sq_abs, sq_abs]
      ring
    simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
    have : ∑ x, ‖w x‖ ^ 2 = ∑ x, (w x).re ^ 2 + ∑ x, (w x).im ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [this, mul_add]
    exact add_le_add hre him
  have main := BGERT_main (fun f : 𝒳 → 𝒜 => pF pA f) (fun f => Finset.prod_nonneg fun _ _ => hpA.1 _)
    K (2 * pA a) (pA a) (by linarith) hpa0 E1 E2 α hα g
  have hcoef : (2 * pA a) ^ (2 - α) * pA a ^ (α - 1) = (2 : ℝ) ^ (2 - α) * pA a := by
    rw [Real.mul_rpow (by norm_num) hpa0, mul_assoc,
      ← Real.rpow_add' hpa0 (by ring_nf; norm_num)]
    ring_nf; rw [Real.rpow_one]
  rw [hcoef] at main
  refine le_trans (le_of_eq ?_) main
  refine Finset.sum_congr rfl fun f _ => ?_
  have : ∑ x, g x * ((if f x = a then 1 else 0) - pA a) = ∑ x, K f x * g x :=
    Finset.sum_congr rfl fun x _ => mul_comm (g x) (K f x)
  rw [this]
