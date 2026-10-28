-- Prove2me | solution 1 for EthierKurtz.tilted_local_limit_smoothed_sum_density
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T01:53:24.681205+00:00
-- url     : https://prove2.me/submissions/4fc7d072-453e-42f2-97be-841db2d6847b

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X0_Lc1

/-! R4 / Q1: local CLT core estimate (pure analysis, Fourier side).
If a characteristic-function-like `χ` satisfies a Cramér-type bound away from 0
(`‖χ s‖ ≤ 1 - κ min(s²,1)`, from a Gaussian component), a second-order Taylor bound with
third-moment remainder, and Gaussian decay `‖χ s‖ ≤ exp(-σ²s²/2)` (smoothing), then the
inverse-Fourier integrals of `χ^N` and of `exp(-N D² s²/2)` differ by `O(1/N) + O((1-κ')^(N-1)/σ)`. -/

open MeasureTheory Real Set Filter

namespace P99bcb804

lemma norm_pow_sub_pow_le' (a b : ℂ) (r : ℝ) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤ (n + 1) * r ^ n * ‖a - b‖ := by
  have hr : 0 ≤ r := (norm_nonneg _).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1)
        = a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [e]
    have hb' : ‖b‖ ^ (n + 1) ≤ r ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hb _
    calc ‖a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1)‖
        ≤ ‖a‖ * ‖a ^ (n + 1) - b ^ (n + 1)‖ + ‖a - b‖ * ‖b‖ ^ (n + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ r * ((n + 1) * r ^ n * ‖a - b‖) + ‖a - b‖ * r ^ (n + 1) := by
          gcongr
      _ = ((n + 1 : ℕ) + 1 : ℝ) * r ^ (n + 1) * ‖a - b‖ := by push_cast; ring

/-- Absolute Gaussian moments: `∫ |x|^k e^{-b x²} = b^{-(k+1)/2} Γ((k+1)/2)`. -/
lemma norm_phase (s x : ℝ) : ‖Complex.exp (-(s * x) * Complex.I)‖ = 1 := by
  have : (-(↑s * ↑x) : ℂ) = ((-(s * x) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma absmom (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| ^ k * exp (-b * x ^ 2) = b ^ (-((k : ℝ) + 1) / 2) * Gamma (((k : ℝ) + 1) / 2) := by
  have hk : (-1 : ℝ) < k := by have := k.cast_nonneg (α := ℝ); linarith
  calc ∫ x : ℝ, |x| ^ k * exp (-b * x ^ 2)
      = ∫ x : ℝ, (fun y : ℝ => y ^ (k : ℝ) * exp (-b * y ^ (2 : ℝ))) |x| := by
        congr 1; funext x; simp only [rpow_natCast, rpow_two, sq_abs]
    _ = 2 * ∫ x in Ioi (0 : ℝ), x ^ (k : ℝ) * exp (-b * x ^ (2 : ℝ)) :=
        integral_comp_abs (f := fun y : ℝ => y ^ (k : ℝ) * exp (-b * y ^ (2 : ℝ)))
    _ = _ := by rw [integral_rpow_mul_exp_neg_mul_rpow two_pos hk hb]; ring

lemma integrable_absmom (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ k * exp (-b * x ^ 2)) := by
  have := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := k.cast_nonneg (α := ℝ); linarith)).norm
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow, abs_exp]

lemma absmom3 {b : ℝ} (hb : 0 < b) : ∫ x : ℝ, |x| ^ 3 * exp (-b * x ^ 2) = 1 / b ^ 2 := by
  rw [absmom 3 hb]
  norm_num [Gamma_two]
  try (rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, rpow_intCast]; simp [zpow_neg])

lemma absmom1 {b : ℝ} (hb : 0 < b) : ∫ x : ℝ, |x| ^ 1 * exp (-b * x ^ 2) = 1 / b := by
  rw [absmom 1 hb]
  norm_num [Gamma_one]
  try (rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, rpow_intCast]; simp)

/-- `e^{-u}` is within `u²` of `1 - u` for `0 ≤ u ≤ 1`. -/
lemma exp_neg_quad {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |exp (-u) - (1 - u)| ≤ u ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1)
  have e : exp (-u) - 1 - -u = exp (-u) - (1 - u) := by ring
  rw [e, neg_sq] at this
  exact this

set_option maxHeartbeats 1000000 in
theorem lclt_core (κ β d1 d2 : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hβ : 0 ≤ β) (hd1 : 0 < d1)
    (hd12 : d1 ≤ d2) :
    ∃ C κ' : ℝ, 0 < C ∧ 0 < κ' ∧ κ' ≤ 1 ∧
      ∀ (χ : ℝ → ℂ) (D2 σ : ℝ) (N : ℕ), Continuous χ → d1 ≤ D2 → D2 ≤ d2 → 0 < σ → 2 ≤ N →
        (∀ s, ‖χ s‖ ≤ 1 - κ * min (s ^ 2) 1) →
        (∀ s, ‖χ s - (1 - D2 * s ^ 2 / 2)‖ ≤ β * |s| ^ 3) →
        (∀ s, ‖χ s‖ ≤ exp (-(σ ^ 2 / 2) * s ^ 2)) →
        ∀ x : ℝ, ‖(∫ s : ℝ, Complex.exp (-(s * x) * Complex.I) * χ s ^ N)
            - ∫ s : ℝ, Complex.exp (-(s * x) * Complex.I) * ((exp (-(D2 * s ^ 2 / 2)) : ℝ) : ℂ) ^ N‖
          ≤ C / N + C * (1 - κ') ^ (N - 1) / σ := by
  have hd2 : 0 < d2 := hd1.trans_le hd12
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (1 / d2) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_left _ _
  have hδd : d2 * δ ≤ 1 := by
    have : δ ≤ 1 / d2 := hδ ▸ min_le_right _ _
    calc d2 * δ ≤ d2 * (1 / d2) := by gcongr
      _ = 1 := by field_simp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min κ (d1 / 2) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ lt_min hκ (by positivity)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = β + d2 ^ 2 / 4 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = κ * δ ^ 2 := ⟨_, rfl⟩
  have hκ'0 : 0 < κ' := by rw [hκ']; positivity
  have hκ'1 : κ' ≤ 1 := by
    rw [hκ']
    calc κ * δ ^ 2 ≤ 1 * 1 ^ 2 := by gcongr
      _ = 1 := by norm_num
  refine ⟨4 * B / c ^ 2 + 2 / (δ * d1) + 3, κ', by positivity, hκ'0, hκ'1, ?_⟩
  intro χ D2 σ N hχc hD1 hD2 hσ hN hfar htay hdec x
  have hD0 : 0 < D2 := hd1.trans_le hD1
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  -- the pointwise bound
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s => exp (-(D2 * s ^ 2 / 2)) := ⟨_, rfl⟩
  obtain ⟨bnd, hbnd⟩ : ∃ bnd : ℝ → ℝ, bnd = fun s =>
    N * B * (|s| ^ 3 * exp (-(c * ((N : ℝ) - 1)) * s ^ 2))
      + (1 - κ') ^ (N - 1) * exp (-(σ ^ 2 / 2) * s ^ 2)
      + 1 / δ * (|s| ^ 1 * exp (-((N : ℝ) * d1 / 2) * s ^ 2)) := ⟨_, rfl⟩
  have hχ1 : ∀ s, ‖χ s‖ ≤ 1 := fun s => by
    have := hfar s
    have : 0 ≤ κ * min (s ^ 2) 1 := mul_nonneg hκ.le (le_min (sq_nonneg _) zero_le_one)
    linarith
  have hpt : ∀ s : ℝ, ‖χ s ^ N - ((g s : ℝ) : ℂ) ^ N‖ ≤ bnd s := by
    intro s
    have hg0 : 0 < g s := by rw [hg]; exact exp_pos _
    have t1 : 0 ≤ N * B * (|s| ^ 3 * exp (-(c * ((N : ℝ) - 1)) * s ^ 2)) := by positivity
    have t2 : 0 ≤ (1 - κ') ^ (N - 1) * exp (-(σ ^ 2 / 2) * s ^ 2) := by
      have : 0 ≤ 1 - κ' := by linarith
      positivity
    have t3 : 0 ≤ 1 / δ * (|s| ^ 1 * exp (-((N : ℝ) * d1 / 2) * s ^ 2)) := by positivity
    by_cases hs : |s| ≤ δ
    · -- near zero
      have hs1 : |s| ≤ 1 := hs.trans hδ1
      have hs2 : s ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg s) hs1
      have hmin : min (s ^ 2) 1 = s ^ 2 := min_eq_left hs2
      have hr1 : ‖χ s‖ ≤ exp (-c * s ^ 2) := by
        calc ‖χ s‖ ≤ 1 - κ * s ^ 2 := by rw [← hmin]; exact hfar s
          _ ≤ exp (-(κ * s ^ 2)) := by linarith [add_one_le_exp (-(κ * s ^ 2))]
          _ ≤ exp (-c * s ^ 2) := by
            apply exp_le_exp.mpr
            have : c ≤ κ := by rw [hc]; exact min_le_left _ _
            nlinarith [sq_nonneg s]
      have hr2 : ‖((g s : ℝ) : ℂ)‖ ≤ exp (-c * s ^ 2) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg0]
        simp only [hg]
        apply exp_le_exp.mpr
        have : c ≤ d1 / 2 := by rw [hc]; exact min_le_right _ _
        nlinarith [sq_nonneg s]
      have hdiff : ‖χ s - ((g s : ℝ) : ℂ)‖ ≤ B * |s| ^ 3 := by
        have hu0 : 0 ≤ D2 * s ^ 2 / 2 := by positivity
        have hu1 : D2 * s ^ 2 / 2 ≤ 1 := by
          have h2 : s ^ 2 ≤ δ := by
            rw [← sq_abs, sq]
            exact (mul_le_mul hs1 hs (abs_nonneg _) zero_le_one).trans (one_mul δ).le
          have h3 : D2 * s ^ 2 ≤ d2 * δ := mul_le_mul hD2 h2 (sq_nonneg s) hd2.le
          linarith
        have hq := exp_neg_quad hu0 hu1
        have e1 : χ s - ((g s : ℝ) : ℂ) = (χ s - (1 - D2 * s ^ 2 / 2))
            - (((g s - (1 - D2 * s ^ 2 / 2) : ℝ)) : ℂ) := by
          push_cast; ring
        rw [e1]
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hq' : |g s - (1 - D2 * s ^ 2 / 2)| ≤ d2 ^ 2 / 4 * |s| ^ 3 := by
          simp only [hg]
          refine hq.trans ?_
          have : s ^ 4 ≤ |s| ^ 3 := by
            rw [show s ^ 4 = |s| ^ 3 * |s| by
              rw [← pow_succ, Even.pow_abs ⟨2, rfl⟩]]
            calc |s| ^ 3 * |s| ≤ |s| ^ 3 * 1 := by gcongr
              _ = |s| ^ 3 := mul_one _
          calc (D2 * s ^ 2 / 2) ^ 2 = D2 ^ 2 / 4 * s ^ 4 := by ring
            _ ≤ d2 ^ 2 / 4 * |s| ^ 3 := by
              have : D2 ^ 2 ≤ d2 ^ 2 := by gcongr
              gcongr
        calc ‖χ s - (1 - D2 * s ^ 2 / 2)‖ + |g s - (1 - D2 * s ^ 2 / 2)|
            ≤ β * |s| ^ 3 + d2 ^ 2 / 4 * |s| ^ 3 := add_le_add (htay s) hq'
          _ = B * |s| ^ 3 := by rw [hB]; ring
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have key := norm_pow_sub_pow_le' (χ s) ((g s : ℝ) : ℂ) _ hr1 hr2 n
      have hexp : exp (-c * s ^ 2) ^ n = exp (-(c * (((n + 1 : ℕ) : ℝ) - 1)) * s ^ 2) := by
        rw [← exp_nat_mul]; congr 1; push_cast; ring
      calc ‖χ s ^ (n + 1) - ((g s : ℝ) : ℂ) ^ (n + 1)‖
          ≤ (n + 1) * exp (-c * s ^ 2) ^ n * ‖χ s - ((g s : ℝ) : ℂ)‖ := key
        _ ≤ (n + 1) * exp (-c * s ^ 2) ^ n * (B * |s| ^ 3) := by gcongr
        _ = ((n + 1 : ℕ) : ℝ) * B * (|s| ^ 3 * exp (-(c * (((n + 1 : ℕ) : ℝ) - 1)) * s ^ 2)) := by
          rw [hexp]; push_cast; ring
        _ ≤ bnd s := by rw [hbnd]; linarith
    · -- away from zero
      push_neg at hs
      have hsq : δ ^ 2 ≤ s ^ 2 := by
        have := pow_le_pow_left₀ hδ0.le hs.le 2; rwa [sq_abs] at this
      have hmin : δ ^ 2 ≤ min (s ^ 2) 1 := le_min hsq (pow_le_one₀ hδ0.le hδ1)
      have hfar' : ‖χ s‖ ≤ 1 - κ' := by
        calc ‖χ s‖ ≤ 1 - κ * min (s ^ 2) 1 := hfar s
          _ ≤ 1 - κ * δ ^ 2 := by gcongr
          _ = 1 - κ' := by rw [hκ']
      have hpow : ‖χ s ^ N‖ ≤ (1 - κ') ^ (N - 1) * exp (-(σ ^ 2 / 2) * s ^ 2) := by
        obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
        rw [norm_pow, pow_succ, Nat.add_sub_cancel]
        gcongr <;> first | exact hfar' | exact hdec s
      have hgN : ‖((g s : ℝ) : ℂ) ^ N‖ ≤ 1 / δ * (|s| ^ 1 * exp (-((N : ℝ) * d1 / 2) * s ^ 2)) := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg0, hg]
        dsimp only
        rw [← exp_nat_mul]
        have h1 : exp (↑N * -(D2 * s ^ 2 / 2)) ≤ exp (-((N : ℝ) * d1 / 2) * s ^ 2) := by
          apply exp_le_exp.mpr
          have : (N : ℝ) * d1 * s ^ 2 ≤ N * D2 * s ^ 2 := by gcongr
          nlinarith
        have h2 : 1 ≤ 1 / δ * |s| ^ 1 := by
          rw [pow_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ hδ0]; linarith
        calc exp (↑N * -(D2 * s ^ 2 / 2)) ≤ exp (-((N : ℝ) * d1 / 2) * s ^ 2) := h1
          _ = 1 * exp (-((N : ℝ) * d1 / 2) * s ^ 2) := (one_mul _).symm
          _ ≤ 1 / δ * |s| ^ 1 * exp (-((N : ℝ) * d1 / 2) * s ^ 2) := by gcongr
          _ = _ := by ring
      calc ‖χ s ^ N - ((g s : ℝ) : ℂ) ^ N‖ ≤ ‖χ s ^ N‖ + ‖((g s : ℝ) : ℂ) ^ N‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add hpow hgN
        _ ≤ bnd s := by rw [hbnd]; linarith
  -- integrability
  have hb1 : 0 < c * ((N : ℝ) - 1) := by positivity
  have hb2 : 0 < σ ^ 2 / 2 := by positivity
  have hb3 : 0 < (N : ℝ) * d1 / 2 := by positivity
  have ibnd : Integrable bnd := by
    rw [hbnd]
    refine ((((integrable_absmom 3 hb1).const_mul (N * B)).add
      ((integrable_exp_neg_mul_sq hb2).const_mul ((1 - κ') ^ (N - 1)))).add
      ((integrable_absmom 1 hb3).const_mul (1 / δ)))
  have iF : Integrable (fun s : ℝ => Complex.exp (-(s * x) * Complex.I) * χ s ^ N) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq hb2)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine Eventually.of_forall fun s => ?_
    rw [norm_mul, norm_phase, one_mul, norm_pow]
    exact (pow_le_of_le_one (norm_nonneg _) (hχ1 s) (by omega)).trans (hdec s)
  have hgD : 0 < D2 / 2 := by positivity
  have iG : Integrable (fun s : ℝ => Complex.exp (-(s * x) * Complex.I)
      * ((exp (-(D2 * s ^ 2 / 2)) : ℝ) : ℂ) ^ N) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq hgD)
      (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine Eventually.of_forall fun s => ?_
    rw [norm_mul, norm_phase, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exp_pos _)]
    refine (pow_le_of_le_one (exp_pos _).le ?_ (by omega)).trans (le_of_eq ?_)
    · exact exp_le_one_iff.mpr (by nlinarith [sq_nonneg s])
    · congr 1; ring
  rw [← integral_sub iF iG]
  have hle : ‖∫ s : ℝ, (Complex.exp (-(s * x) * Complex.I) * χ s ^ N
      - Complex.exp (-(s * x) * Complex.I) * ((exp (-(D2 * s ^ 2 / 2)) : ℝ) : ℂ) ^ N)‖
      ≤ ∫ s, bnd s := by
    refine norm_integral_le_of_norm_le ibnd (Eventually.of_forall fun s => ?_)
    rw [← mul_sub, norm_mul, norm_phase, one_mul]
    have := hpt s
    simp only [hg] at this
    exact this
  refine hle.trans ?_
  have hI : ∫ s, bnd s = N * B * (1 / (c * ((N : ℝ) - 1)) ^ 2)
      + (1 - κ') ^ (N - 1) * √(π / (σ ^ 2 / 2)) + 1 / δ * (1 / ((N : ℝ) * d1 / 2)) := by
    simp only [hbnd]
    rw [integral_add ?_ ((integrable_absmom 1 hb3).const_mul _),
      integral_add ((integrable_absmom 3 hb1).const_mul _)
        ((integrable_exp_neg_mul_sq hb2).const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, absmom3 hb1, absmom1 hb3,
      integral_gaussian]
    all_goals first
      | exact ((integrable_absmom 3 hb1).const_mul _).add
          ((integrable_exp_neg_mul_sq hb2).const_mul _)
      | simp only [one_div, inv_pow]
  rw [hI]
  have hκ0 : 0 ≤ 1 - κ' := by linarith
  have hP : 0 ≤ (1 - κ') ^ (N - 1) := pow_nonneg hκ0 _
  have hsq : √(π / (σ ^ 2 / 2)) ≤ 3 / σ := by
    rw [show π / (σ ^ 2 / 2) = (2 * π) / σ ^ 2 by field_simp, sqrt_div' _ (sq_nonneg σ),
      sqrt_sq hσ.le]
    gcongr
    rw [sqrt_le_left (by norm_num)]
    nlinarith [pi_lt_d2]
  have h1 : N * B * (1 / (c * ((N : ℝ) - 1)) ^ 2) ≤ 4 * B / c ^ 2 / N := by
    rw [mul_pow, mul_one_div, div_div, div_le_div_iff₀
      (mul_pos (pow_pos hc0 2) (pow_pos (by linarith : (0 : ℝ) < N - 1) 2)) (by positivity)]
    have : (N : ℝ) * N ≤ 4 * ((N : ℝ) - 1) ^ 2 := by
      have e : 4 * ((N : ℝ) - 1) ^ 2 - N * N = (3 * N - 2) * (N - 2) := by ring
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * N - 2) (by linarith : (0 : ℝ) ≤ N - 2)
      linarith
    calc N * B * (c ^ 2 * N) = B * c ^ 2 * (N * N) := by ring
      _ ≤ B * c ^ 2 * (4 * ((N : ℝ) - 1) ^ 2) := by gcongr
      _ = 4 * B * (c ^ 2 * ((N : ℝ) - 1) ^ 2) := by ring
  have h3 : 1 / δ * (1 / ((N : ℝ) * d1 / 2)) = 2 / (δ * d1) / N := by
    field_simp
  have hC1 : 4 * B / c ^ 2 / N + 2 / (δ * d1) / N ≤ (4 * B / c ^ 2 + 2 / (δ * d1) + 3) / N := by
    rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hNpos.le
  have hC2 : (1 - κ') ^ (N - 1) * √(π / (σ ^ 2 / 2))
      ≤ (4 * B / c ^ 2 + 2 / (δ * d1) + 3) * (1 - κ') ^ (N - 1) / σ := by
    calc (1 - κ') ^ (N - 1) * √(π / (σ ^ 2 / 2)) ≤ (1 - κ') ^ (N - 1) * (3 / σ) := by gcongr
      _ = 3 * (1 - κ') ^ (N - 1) / σ := by ring
      _ ≤ _ := by
        gcongr
        have : 0 ≤ 4 * B / c ^ 2 + 2 / (δ * d1) := by positivity
        linarith
  linarith

end P99bcb804

end X0_Lc1

section X1_Lc2

/-! R4 / Q1-Q2 inputs: hypotheses of `lclt_core` for concrete laws.
* `phase3`: `‖e^{iu} - (1 + iu - u²/2)‖ ≤ 4|u|³`;
* `charFun_taylor3`: second-order Taylor bound for a centred law with third absolute moment;
* `charFun_mixM`, `norm_charFun_gmix_le`, `gmix_far`: a Gaussian component gives
  `‖χ s‖ ≤ 1 - κ min(s²,1)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma phase3 (u : ℝ) :
    ‖Complex.exp (u * Complex.I) - (1 + u * Complex.I - u ^ 2 / 2)‖ ≤ 4 * |u| ^ 3 := by
  have hn : ‖(u : ℂ) * Complex.I‖ = |u| := by simp
  by_cases hu : |u| ≤ 1
  · have h := Complex.exp_bound (x := (u : ℂ) * Complex.I) (n := 3) (by rw [hn]; exact hu)
      (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
        = 1 + u * Complex.I - u ^ 2 / 2 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hs, hn] at h
    refine h.trans ?_
    have : 0 ≤ |u| ^ 3 := by positivity
    norm_num
    nlinarith
  · push_neg at hu
    have h1 : ‖Complex.exp (u * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I u
    have h2 : ‖(1 : ℂ) + u * Complex.I - u ^ 2 / 2‖ ≤ 1 + |u| + u ^ 2 / 2 := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
      · rw [norm_one, hn]
      · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        norm_num
    set t := |u| with ht
    have hu2 : u ^ 2 = t ^ 2 := (sq_abs u).symm
    have ht0 : 0 < t := by linarith
    have ht2 : t ≤ t ^ 2 := by nlinarith [mul_pos ht0 (by linarith : (0 : ℝ) < t - 1)]
    have ht3 : t ^ 2 ≤ t ^ 3 := by
      nlinarith [mul_pos (pow_pos ht0 2) (by linarith : (0 : ℝ) < t - 1)]
    calc ‖Complex.exp (u * Complex.I) - (1 + u * Complex.I - u ^ 2 / 2)‖
        ≤ ‖Complex.exp (u * Complex.I)‖ + ‖(1 : ℂ) + u * Complex.I - u ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + t + t ^ 2 / 2) := by rw [h1, ← hu2]; linarith
      _ ≤ 4 * t ^ 3 := by linarith

lemma charFun_taylor3 (H : Measure ℝ) [IsProbabilityMeasure H]
    (h3 : Integrable (fun y => |y| ^ 3) H) (h0 : ∫ y, y ∂H = 0) (s : ℝ) :
    ‖charFun H s - (1 - (∫ y, y ^ 2 ∂H) * s ^ 2 / 2)‖ ≤ 4 * (∫ y, |y| ^ 3 ∂H) * |s| ^ 3 := by
  have i1 : Integrable (fun y : ℝ => y) H := by
    refine Integrable.mono' ((integrable_const 1).add h3) (by fun_prop) ?_
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    by_cases hy : |y| ≤ 1
    · have : 0 ≤ |y| ^ 3 := by positivity
      simp only [Pi.add_apply]; linarith
    · push_neg at hy
      have : |y| ≤ |y| ^ 3 := by
        simpa using pow_le_pow_right₀ hy.le (by norm_num : 1 ≤ 3)
      simp only [Pi.add_apply]; linarith
  have i2 : Integrable (fun y : ℝ => y ^ 2) H := by
    refine Integrable.mono' ((integrable_const 1).add h3) (by fun_prop) ?_
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg y), ← sq_abs]
    by_cases hy : |y| ≤ 1
    · have : 0 ≤ |y| ^ 3 := by positivity
      have : |y| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
      simp only [Pi.add_apply]; linarith
    · push_neg at hy
      have : |y| ^ 2 ≤ |y| ^ 3 := pow_le_pow_right₀ hy.le (by norm_num)
      simp only [Pi.add_apply]; linarith
  have ipoly : Integrable (fun y : ℝ => (((1 - s ^ 2 / 2 * y ^ 2 : ℝ)) : ℂ)
      + ((s * y : ℝ) : ℂ) * Complex.I) H := by
    refine Integrable.add ?_ ?_
    · exact ((integrable_const 1).sub (i2.const_mul _)).ofReal
    · exact (i1.const_mul s).ofReal.mul_const _
  have hpoly : ∫ y, ((((1 - s ^ 2 / 2 * y ^ 2 : ℝ)) : ℂ) + ((s * y : ℝ) : ℂ) * Complex.I) ∂H
      = 1 - ((∫ y, y ^ 2 ∂H : ℝ) : ℂ) * s ^ 2 / 2 := by
    rw [integral_add ((integrable_const 1).sub (i2.const_mul _)).ofReal
      ((i1.const_mul s).ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal, integral_sub (integrable_const 1) (i2.const_mul _),
      integral_const_mul, integral_const_mul, h0, integral_const]
    have hu : H.real univ = 1 := by simp [Measure.real]
    rw [hu]
    simp only [smul_eq_mul, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    push_cast
    ring
  have ichar : Integrable (fun y : ℝ => Complex.exp (((s * y : ℝ) : ℂ) * Complex.I)) H := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun y => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have e : charFun H s - (1 - (∫ y, y ^ 2 ∂H) * s ^ 2 / 2)
      = ∫ y, (Complex.exp (((s * y : ℝ) : ℂ) * Complex.I)
        - ((((1 - s ^ 2 / 2 * y ^ 2 : ℝ)) : ℂ) + ((s * y : ℝ) : ℂ) * Complex.I)) ∂H := by
    rw [integral_sub ichar ipoly, hpoly, charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [e]
  have hb : ∀ y : ℝ, ‖Complex.exp (((s * y : ℝ) : ℂ) * Complex.I)
      - ((((1 - s ^ 2 / 2 * y ^ 2 : ℝ)) : ℂ) + ((s * y : ℝ) : ℂ) * Complex.I)‖
      ≤ 4 * |s| ^ 3 * |y| ^ 3 := by
    intro y
    have := phase3 (s * y)
    have e2 : (((1 - s ^ 2 / 2 * y ^ 2 : ℝ)) : ℂ) + ((s * y : ℝ) : ℂ) * Complex.I
        = 1 + ((s * y : ℝ) : ℂ) * Complex.I - ((s * y : ℝ) : ℂ) ^ 2 / 2 := by push_cast; ring
    rw [e2]
    refine this.trans (le_of_eq ?_)
    rw [abs_mul, mul_pow]; ring
  refine (norm_integral_le_of_norm_le (h3.const_mul (4 * |s| ^ 3))
    (Eventually.of_forall hb)).trans (le_of_eq ?_)
  rw [integral_const_mul]; ring

lemma gmix_far {p a : ℝ} (hp0 : 0 ≤ p) (ha : 0 ≤ a) (s : ℝ) :
    p * exp (-(a * s ^ 2)) + (1 - p) ≤ 1 - p * (1 - exp (-a)) * min (s ^ 2) 1 := by
  have key : exp (-(a * s ^ 2)) ≤ 1 - (1 - exp (-a)) * min (s ^ 2) 1 := by
    by_cases hs : s ^ 2 ≤ 1
    · rw [min_eq_left hs]
      have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-a))
        (by linarith : (0 : ℝ) ≤ 1 - s ^ 2) (sq_nonneg s) (by ring : (1 - s ^ 2) + s ^ 2 = 1)
      simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at hc
      have : s ^ 2 * -a = -(a * s ^ 2) := by ring
      rw [this] at hc
      linarith
    · push_neg at hs
      rw [min_eq_right hs.le]
      have : exp (-(a * s ^ 2)) ≤ exp (-a) := exp_le_exp.mpr (by nlinarith)
      linarith
  nlinarith

end P99bcb804

end X1_Lc2

section X2_Lc3

/-! R4 / Q2: density of a Gaussian-smoothed law by Fourier (Fubini, no inversion theorem).
* `gauss_ft`: `∫ e^{-isz} e^{-v s²/2} ds = 2π φ_v(z)`;
* `dens_formula`: `∫ φ_v(x-y) dν(y) = (1/2π) ∫ e^{-isx} charFun ν s e^{-v s²/2} ds`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma gauss_ft {v : ℝ≥0} (hv : v ≠ 0) (z : ℝ) :
    ∫ s : ℝ, Complex.exp (-(s * z) * Complex.I) * ((exp (-((v : ℝ) / 2 * s ^ 2)) : ℝ) : ℂ)
      = ((2 * π * gaussianPDFReal 0 v z : ℝ) : ℂ) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hb : 0 < (((v : ℝ) / 2 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  have h := fourierIntegral_gaussian hb (-(z : ℂ))
  have hL : ∀ s : ℝ, Complex.exp (-(s * z) * Complex.I) * ((exp (-((v : ℝ) / 2 * s ^ 2)) : ℝ) : ℂ)
      = Complex.exp (Complex.I * -(z : ℂ) * s) * Complex.exp (-(((v : ℝ) / 2 : ℝ) : ℂ) * s ^ 2) := by
    intro s
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  simp_rw [hL]
  rw [h]
  have h1 : ((π : ℂ) / (((v : ℝ) / 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * π / v) : ℝ) : ℂ) := by
    rw [show ((π : ℂ) / (((v : ℝ) / 2 : ℝ) : ℂ)) = ((2 * π / v : ℝ) : ℂ) by
      push_cast; field_simp, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  have h2 : Complex.exp (-(-(z : ℂ)) ^ 2 / (4 * (((v : ℝ) / 2 : ℝ) : ℂ)))
      = ((exp (-z ^ 2 / (2 * v)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
    ring
  rw [h1, h2, ← Complex.ofReal_mul]
  congr 1
  have hs : √(2 * π / v) * √(2 * π * v) = 2 * π := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * π / v * (2 * π * v) = (2 * π) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hpos : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianPDFReal, sub_zero]
  calc √(2 * π / v) * exp (-z ^ 2 / (2 * v))
      = √(2 * π / v) * √(2 * π * v) * (√(2 * π * v))⁻¹ * exp (-z ^ 2 / (2 * v)) := by
        field_simp
    _ = _ := by rw [hs]; ring

lemma dens_formula (ν : Measure ℝ) [IsProbabilityMeasure ν] {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    ((∫ y, gaussianPDFReal 0 v (x - y) ∂ν : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ s : ℝ, Complex.exp (-(s * x) * Complex.I) * charFun ν s
          * ((exp (-((v : ℝ) / 2 * s ^ 2)) : ℝ) : ℂ) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hb : (0 : ℝ) < (v : ℝ) / 2 := by positivity
  set g : ℝ → ℝ := fun s => exp (-((v : ℝ) / 2 * s ^ 2)) with hg
  have ig : Integrable g := by
    have := integrable_exp_neg_mul_sq hb
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only [hg, neg_mul]
  have hpi : (2 * π : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact_mod_cast this.ne'
  -- step 1: rewrite the density by `gauss_ft`
  have step1 : ∀ y : ℝ, ((gaussianPDFReal 0 v (x - y) : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ s : ℝ, Complex.exp (-(s * (x - y)) * Complex.I) * ((g s : ℝ) : ℂ) := by
    intro y
    rw [hg]
    simp only
    have := gauss_ft hv (x - y)
    push_cast at this ⊢
    rw [this]
    field_simp
  rw [← integral_complex_ofReal]
  simp_rw [step1]
  rw [integral_const_mul]
  congr 1
  -- step 2: Fubini
  have hF : Integrable (Function.uncurry fun (y s : ℝ) =>
      Complex.exp (-(s * (x - y)) * Complex.I) * ((g s : ℝ) : ℂ)) (ν.prod volume) := by
    have hb' : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * g p.2) (ν.prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod ig
    refine hb'.mono' (Continuous.aestronglyMeasurable (by rw [hg]; fun_prop)) ?_
    refine Eventually.of_forall fun p => ?_
    change ‖Complex.exp (-(↑p.2 * (↑x - ↑p.1)) * Complex.I) * ((g p.2 : ℝ) : ℂ)‖ ≤ 1 * g p.2
    rw [one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by rw [hg]; exact exp_pos _)]
    have : (-(↑p.2 * (↑x - ↑p.1)) : ℂ) = ((-(p.2 * (x - p.1)) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [integral_integral_swap hF]
  congr 1
  funext s
  have e : ∀ y : ℝ, Complex.exp (-(s * (x - y)) * Complex.I) * ((g s : ℝ) : ℂ)
      = (Complex.exp (-(s * x) * Complex.I) * ((g s : ℝ) : ℂ)) * Complex.exp (s * y * Complex.I) := by
    intro y
    rw [mul_comm _ (Complex.exp _), ← mul_assoc, ← Complex.exp_add]
    congr 1
    · congr 1; ring
  simp_rw [e]
  rw [integral_const_mul, ← charFun_apply_real]
  rw [hg]
  ring

end P99bcb804

end X2_Lc3

section X3_Lc4

/-! R4 / Q2 (rest): Gaussian smoothing and the local CLT for densities.
* `conv_gauss_eq`: `ν ∗ N(0,v)` has density `x ↦ ∫⁻ φ_v(x-y) dν`;
* `lint_dens`: that density as `ofReal` of a Bochner integral;
* `charFun_sumLaw`: characteristic function of an iid sum;
* `lclt_dens`: density of (iid sum of `H0`) ∗ `N(0,Nσ²)` is within `C/N + C(1-κ')^(N-1)/σ` of `φ_{N D2}`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma charFun_sumLaw (H : Measure ℝ) [IsProbabilityMeasure H] (ι : Type) [Fintype ι] (s : ℝ) :
    charFun ((Measure.pi fun _ : ι => H).map (fun p => ∑ i, p i)) s
      = charFun H s ^ Fintype.card ι := by
  rw [charFun_map_sum_pi_eq_prod]
  simp [Finset.prod_const]

set_option maxHeartbeats 1000000 in
theorem lclt_dens (κ β d1 d2 : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hβ : 0 ≤ β) (hd1 : 0 < d1)
    (hd12 : d1 ≤ d2) :
    ∃ C κ' : ℝ, 0 < C ∧ 0 < κ' ∧ κ' ≤ 1 ∧
      ∀ (H0 : Measure ℝ) [IsProbabilityMeasure H0] (ι : Type) [Fintype ι] (D2 σ : ℝ),
        d1 ≤ D2 → D2 ≤ d2 → 0 < σ → 2 ≤ Fintype.card ι →
        (∀ s, ‖charFun H0 s * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ)‖ ≤ 1 - κ * min (s ^ 2) 1) →
        (∀ s, ‖charFun H0 s * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ) - (1 - D2 * s ^ 2 / 2)‖
          ≤ β * |s| ^ 3) →
        ∀ x : ℝ, |(∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (x - y)
              ∂((Measure.pi fun _ : ι => H0).map (fun p => ∑ i, p i)))
            - gaussianPDFReal 0 (Fintype.card ι * D2).toNNReal x|
          ≤ C / Fintype.card ι + C * (1 - κ') ^ (Fintype.card ι - 1) / σ := by
  obtain ⟨C, κ', hC, hκ'0, hκ'1, H⟩ := lclt_core κ β d1 d2 hκ hκ1 hβ hd1 hd12
  refine ⟨C, κ', hC, hκ'0, hκ'1, ?_⟩
  intro H0 _ ι _ D2 σ hD1 hD2 hσ hN hfar htay x
  set N := Fintype.card ι with hNdef
  set ν := (Measure.pi fun _ : ι => H0).map (fun p => ∑ i, p i) with hν
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hD0 : 0 < D2 := hd1.trans_le hD1
  have hv0 : (0 : ℝ) ≤ N * σ ^ 2 := by positivity
  have hw0 : (0 : ℝ) ≤ N * D2 := by positivity
  have hv : (N * σ ^ 2 : ℝ).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have hw : (N * D2 : ℝ).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  set χ : ℝ → ℂ := fun s => charFun H0 s * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ) with hχ
  have hcont : Continuous χ := by
    rw [hχ]
    exact continuous_charFun.mul (Complex.continuous_ofReal.comp (by fun_prop))
  have hdecay : ∀ s, ‖χ s‖ ≤ exp (-(σ ^ 2 / 2) * s ^ 2) := by
    intro s
    rw [hχ]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    calc ‖charFun H0 s‖ * exp (-(σ ^ 2 / 2) * s ^ 2) ≤ 1 * exp (-(σ ^ 2 / 2) * s ^ 2) := by
          gcongr; exact norm_charFun_le_one s
      _ = _ := one_mul _
  have hb := H χ D2 σ N hcont hD1 hD2 hσ hN hfar htay hdecay x
  have e1 := dens_formula ν hv x
  have e2 := gauss_ft hw x
  rw [Real.coe_toNNReal _ hv0] at e1
  rw [Real.coe_toNNReal _ hw0] at e2
  have k1 : ∀ s : ℝ, Complex.exp (-(s * x) * Complex.I) * charFun ν s
      * ((exp (-((N * σ ^ 2) / 2 * s ^ 2)) : ℝ) : ℂ)
      = Complex.exp (-(s * x) * Complex.I) * χ s ^ N := by
    intro s
    rw [hν, charFun_sumLaw, hχ]
    simp only
    rw [mul_assoc, mul_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 3
    ring
  have k2 : ∀ s : ℝ, Complex.exp (-(s * x) * Complex.I)
      * ((exp (-((N * D2) / 2 * s ^ 2)) : ℝ) : ℂ)
      = Complex.exp (-(s * x) * Complex.I) * ((exp (-(D2 * s ^ 2 / 2)) : ℝ) : ℂ) ^ N := by
    intro s
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 3
    ring
  simp_rw [k1] at e1
  simp_rw [k2] at e2
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have key : (((∫ y, gaussianPDFReal 0 (N * σ ^ 2).toNNReal (x - y) ∂ν)
      - gaussianPDFReal 0 (N * D2).toNNReal x : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ((∫ s : ℝ, Complex.exp (-(s * x) * Complex.I) * χ s ^ N)
        - ∫ s : ℝ, Complex.exp (-(s * x) * Complex.I)
          * ((exp (-(D2 * s ^ 2 / 2)) : ℝ) : ℂ) ^ N) := by
    rw [Complex.ofReal_sub, e1, e2, mul_sub]
    congr 1
    have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    push_cast
    field_simp
  have : |(∫ y, gaussianPDFReal 0 (N * σ ^ 2).toNNReal (x - y) ∂ν)
      - gaussianPDFReal 0 (N * D2).toNNReal x|
      = ‖(((∫ y, gaussianPDFReal 0 (N * σ ^ 2).toNNReal (x - y) ∂ν)
      - gaussianPDFReal 0 (N * D2).toNNReal x : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [this, key, norm_mul]
  have hn : ‖(1 / (2 * π) : ℂ)‖ ≤ 1 := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_one hpi]
    have := Real.pi_gt_three
    linarith
  calc ‖(1 / (2 * π) : ℂ)‖ * _ ≤ 1 * _ := by gcongr
    _ = _ := one_mul _
    _ ≤ _ := hb

end P99bcb804

end X3_Lc4

section X4_Tl1

/-! R4 / Q3: Esscher tilt of the smoothed sum density, for laws with an exponential moment.
* `pi_wdE`, `com_int`: change of measure from `pi F` to `pi (F.tilted (t·))`;
* `sq_complete`: `φ_v(u) e^{tu} = e^{t²v/2} φ_v(u - tv)`;
* `tilt_dens`: `∫ φ_v(a-y) d(ΣF) = M(t)^N e^{t²v/2} e^{-ta} ∫ φ_v(a - tv - y) d(ΣF_t)`;
* `sum_center`: shifting every summand by `-c` shifts the sum law by `-N c`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Tl1

variable {ι : Type} [Fintype ι]

lemma pi_wdE (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ → ℝ≥0∞) (hρ : Measurable ρ)
    [IsProbabilityMeasure (μ.withDensity ρ)] :
    Measure.pi (fun _ : ι => μ.withDensity ρ) =
      (Measure.pi fun _ : ι => μ).withDensity (fun x => ∏ i, ρ (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, ρ (x i)) =
      fun x => ∏ i, (s i).indicator ρ (x i) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ι → ℝ) => (s i).indicator ρ (x i))
    (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun i => (s i).indicator ρ)
      (fun i => (hρ.indicator (hs i)).aemeasurable))
    (fun i => (hρ.indicator (hs i)).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  exact (measurePreserving_eval (fun _ : ι => μ) i).lintegral_comp (hρ.indicator (hs i))

/-- Change of measure to the tilted product law (integral form, any integrand). -/
lemma com_int (F : Measure ℝ) [IsProbabilityMeasure F] {t : ℝ}
    (hI : Integrable (fun x => exp (t * x)) F) (g : (ι → ℝ) → ℝ) :
    ∫ x, g x ∂(Measure.pi fun _ : ι => F) =
      ∫ x, mgf (fun y : ℝ => y) F t ^ Fintype.card ι * exp (-(t * ∑ i, x i)) * g x
        ∂(Measure.pi fun _ : ι => F.tilted (fun x => t * x)) := by
  set M := mgf (fun y : ℝ => y) F t with hMdef
  have hM : 0 < M := mgf_pos hI
  set ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (t * x) / M) with hρdef
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hFt : F.tilted (fun x => t * x) = F.withDensity ρ := rfl
  have : IsProbabilityMeasure (F.withDensity ρ) := hFt ▸ isProbabilityMeasure_tilted hI
  rw [hFt, pi_wdE F ρ hρ, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : ι → ℝ => ∏ i, ρ (x i)) from
      Finset.measurable_prod _ fun i _ => hρ.comp (measurable_pi_apply i))
    (ae_of_all _ fun x => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_prod]
  simp only [hρdef, ENNReal.toReal_ofReal (div_pos (exp_pos _) hM).le]
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
    ← Finset.mul_sum]
  have hMm : M ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hM.ne'
  rw [← mul_assoc, ← mul_assoc, div_mul_eq_mul_div, mul_div_assoc, div_self hMm, mul_one,
    ← exp_add, add_neg_cancel, exp_zero, one_mul]

lemma sq_complete (v : ℝ≥0) (t u : ℝ) :
    gaussianPDFReal 0 v u * exp (t * u) = exp (t ^ 2 * v / 2) * gaussianPDFReal 0 v (u - t * v) := by
  by_cases hv : v = 0
  · subst hv; simp [gaussianPDFReal_zero_var]
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  simp only [gaussianPDFReal, sub_zero]
  rw [mul_assoc, ← exp_add, mul_left_comm, ← exp_add]
  congr 2
  field_simp
  ring

lemma tilt_dens (F : Measure ℝ) [IsProbabilityMeasure F] {t : ℝ}
    (hI : Integrable (fun x => exp (t * x)) F) (v : ℝ≥0) (a : ℝ) :
    ∫ y, gaussianPDFReal 0 v (a - y) ∂((Measure.pi fun _ : ι => F).map (fun p => ∑ i, p i))
      = mgf (fun y : ℝ => y) F t ^ Fintype.card ι * exp (t ^ 2 * v / 2) * exp (-(t * a)) *
        ∫ y, gaussianPDFReal 0 v (a - t * v - y)
          ∂((Measure.pi fun _ : ι => F.tilted (fun x => t * x)).map (fun p => ∑ i, p i)) := by
  have hs : Measurable (fun p : ι → ℝ => ∑ i, p i) := by fun_prop
  have hg : ∀ b : ℝ, Measurable (fun y => gaussianPDFReal 0 v (b - y)) := fun b =>
    (measurable_gaussianPDFReal 0 v).comp (measurable_const_sub b)
  rw [integral_map hs.aemeasurable (hg a).aestronglyMeasurable,
    integral_map hs.aemeasurable (hg _).aestronglyMeasurable, com_int F hI, ← integral_const_mul]
  congr 1
  funext x
  have h := sq_complete v t (a - ∑ i, x i)
  have e : exp (-(t * ∑ i, x i)) = exp (-(t * a)) * exp (t * (a - ∑ i, x i)) := by
    rw [← exp_add]; congr 1; ring
  rw [e, show a - t * v - ∑ i, x i = a - ∑ i, x i - t * v by ring]
  calc mgf (fun y : ℝ => y) F t ^ Fintype.card ι * (exp (-(t * a)) * exp (t * (a - ∑ i, x i)))
        * gaussianPDFReal 0 v (a - ∑ i, x i)
      = mgf (fun y : ℝ => y) F t ^ Fintype.card ι * exp (-(t * a))
        * (gaussianPDFReal 0 v (a - ∑ i, x i) * exp (t * (a - ∑ i, x i))) := by ring
    _ = _ := by rw [h]; ring

lemma sum_center (H : Measure ℝ) [IsProbabilityMeasure H] (c : ℝ) :
    (Measure.pi fun _ : ι => H.map (fun x => x - c)).map (fun p => ∑ i, p i)
      = ((Measure.pi fun _ : ι => H).map (fun p => ∑ i, p i)).map
          (fun y => y - Fintype.card ι * c) := by
  rw [← Measure.pi_map_pi (fun _ => (measurable_sub_const c).aemeasurable),
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [Finset.sum_sub_distrib]

end Tl1

end P99bcb804

end X4_Tl1

section X5_Cg1

/-! R4 / Q3: cumulants of a law with exponential moments (uniform local bounds).
* `taylor_an`: Taylor with Lagrange remainder for a function analytic on a neighbourhood;
* `itd_itd`: `iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (k + m) f`;
* `ioo_sub_int`, `an_cgf`, `V_zero`: the cgf `ψ` is analytic on `(-a0, a0)` and `ψ''(0) = 1`;
* `cum_local`: `∃ t1 B`, on `[-2t1, 2t1]`: `1/2 ≤ ψ'' ≤ 2`, `|ψ'''| ≤ B`;
* `cum_T0/T1/T2`: Taylor bounds of `ψ'', ψ', ψ` on `[-t1, t1]`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal Nat

namespace P99bcb804

section Cum

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma ioo_sub_int (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) :
    Ioo (-a0) a0 ⊆ interior (integrableExpSet (fun x : ℝ => x) G) :=
  interior_maximal (fun t ht => hexp t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)) isOpen_Ioo

lemma an_cgf (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) (k : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv k (cgf (fun x : ℝ => x) G)) (Ioo (-a0) a0) := by
  rw [iteratedDeriv_eq_iterate]
  exact (analyticOnNhd_cgf.mono (ioo_sub_int hexp)).iterated_deriv k

end Cum

end P99bcb804

end X5_Cg1

section X6_Cg2

/-! R4 / Q3: the tilted law of a Gaussian-component mixture keeps a Gaussian component.
* `cf_tilt`: `charFun (G.tilted (t·)) s = complexMGF id G (t + s i) / mgf id G t`;
* `cmgf_mix`, `mgf_mix`: (complex) mgf of `p•N + (1-p)•F2` is the mixture of the mgfs;
* `norm_cf_tilt_mix`: `‖charFun G_t s‖ ≤ p_t e^{-v s²/2} + (1 - p_t)`, `p_t = p M_N(t)/M_G(t)`;
* `norm_cf_shift`: centring does not change `‖charFun‖`;
* `pt_lower_g`: `p_t ≥ p/2` for `|t| ≤ t2`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma cf_tilt (G : Measure ℝ) (t s : ℝ) :
    charFun (G.tilted (fun x => t * x)) s
      = complexMGF (fun x : ℝ => x) G (t + s * Complex.I) / (mgf (fun x : ℝ => x) G t : ℂ) := by
  rw [charFun_apply_real, integral_tilted, complexMGF, mgf, div_eq_mul_inv, ← integral_mul_const]
  congr 1
  funext x
  rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_exp]
  have : Complex.exp (((t * x : ℝ) : ℂ)) * Complex.exp (↑s * ↑x * Complex.I)
      = Complex.exp ((↑t + ↑s * Complex.I) * ↑x) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [div_eq_mul_inv, mul_right_comm, this]

section Mix

variable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N F2 : Measure ℝ) [IsProbabilityMeasure N]
  [IsProbabilityMeasure F2]

include hp0 hp1 in
lemma cmgf_mix (z : ℂ)
    (hI : Integrable (fun x : ℝ => exp (z.re * x)) (ENNReal.ofReal p • N + ENNReal.ofReal (1 - p) • F2)) :
    complexMGF (fun x : ℝ => x) (ENNReal.ofReal p • N + ENNReal.ofReal (1 - p) • F2) z
      = (p : ℂ) * complexMGF (fun x : ℝ => x) N z
        + ((1 - p : ℝ) : ℂ) * complexMGF (fun x : ℝ => x) F2 z := by
  have hc : Integrable (fun x : ℝ => Complex.exp (z * x))
      (ENNReal.ofReal p • N + ENNReal.ofReal (1 - p) • F2) := by
    refine hI.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]
    simp
  rw [complexMGF, integral_add_measure (hc.mono_measure (Measure.le_add_right le_rfl))
    (hc.mono_measure (Measure.le_add_left le_rfl)), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith), complexMGF, complexMGF]
  simp only [Complex.real_smul]

include hp0 hp1 in
lemma mgf_mix (t : ℝ)
    (hI : Integrable (fun x : ℝ => exp (t * x)) (ENNReal.ofReal p • N + ENNReal.ofReal (1 - p) • F2)) :
    mgf (fun x : ℝ => x) (ENNReal.ofReal p • N + ENNReal.ofReal (1 - p) • F2) t
      = p * mgf (fun x : ℝ => x) N t + (1 - p) * mgf (fun x : ℝ => x) F2 t := by
  rw [mgf, integral_add_measure (hI.mono_measure (Measure.le_add_right le_rfl))
    (hI.mono_measure (Measure.le_add_left le_rfl)), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith), mgf, mgf]
  simp only [smul_eq_mul]

end Mix

lemma norm_cf_tilt_mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ)
    [IsProbabilityMeasure F2]
    [IsProbabilityMeasure (ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)]
    (t s : ℝ)
    (hI : Integrable (fun x : ℝ => exp (t * x))
      (ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)) :
    ‖charFun ((ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2).tilted
        (fun x => t * x)) s‖
      ≤ p * mgf (fun x : ℝ => x) (gaussianReal m v) t
          / mgf (fun x : ℝ => x) (ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2) t
          * exp (-((v : ℝ) / 2 * s ^ 2))
        + (1 - p * mgf (fun x : ℝ => x) (gaussianReal m v) t
          / mgf (fun x : ℝ => x) (ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2) t) := by
  set G := ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2 with hG
  set A := mgf (fun x : ℝ => x) (gaussianReal m v) t with hA
  set Bf := mgf (fun x : ℝ => x) F2 t with hBf
  set M := mgf (fun x : ℝ => x) G t with hM
  have hMpos : 0 < M := mgf_pos hI
  have hMe : M = p * A + (1 - p) * Bf := mgf_mix p hp0 hp1 _ _ t hI
  have hBf0 : 0 ≤ Bf := mgf_nonneg
  have hAe : A = exp (m * t + v * t ^ 2 / 2) := by
    rw [hA]; exact congrFun mgf_id_gaussianReal t
  set z : ℂ := (t : ℂ) + s * Complex.I with hz
  have hzre : z.re = t := by simp [hz]
  rw [cf_tilt, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
  rw [cmgf_mix p hp0 hp1 _ _ z (by rw [hzre]; exact hI)]
  have hN : complexMGF (fun x : ℝ => x) (gaussianReal m v) z
      = Complex.exp (z * m + v * z ^ 2 / 2) := complexMGF_id_gaussianReal z
  have hNn : ‖complexMGF (fun x : ℝ => x) (gaussianReal m v) z‖ = A * exp (-((v : ℝ) / 2 * s ^ 2)) := by
    rw [hN, Complex.norm_exp, hAe, ← exp_add]
    congr 1
    simp [hz, sq]
    ring
  have hFn : ‖complexMGF (fun x : ℝ => x) F2 z‖ ≤ Bf := by
    have := norm_complexMGF_le_mgf (X := fun x : ℝ => x) (μ := F2) (z := z)
    rwa [hzre] at this
  have hnum : ‖(p : ℂ) * complexMGF (fun x : ℝ => x) (gaussianReal m v) z
      + ((1 - p : ℝ) : ℂ) * complexMGF (fun x : ℝ => x) F2 z‖
      ≤ p * (A * exp (-((v : ℝ) / 2 * s ^ 2))) + (1 - p) * Bf := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hp0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - p), hNn]
    gcongr
  calc _ ≤ (p * (A * exp (-((v : ℝ) / 2 * s ^ 2))) + (1 - p) * Bf) / M := by gcongr
    _ = _ := by
      rw [hMe] at hMpos ⊢
      field_simp
      ring

lemma norm_cf_shift (μ : Measure ℝ) (c s : ℝ) :
    ‖charFun (μ.map (fun x => x - c)) s‖ = ‖charFun μ s‖ := by
  have e : (fun x : ℝ => x - c) = (· + (-c)) := by funext x; ring
  rw [e, charFun_map_add_const, norm_mul]
  have : ‖Complex.exp (((inner ℝ (-c) s : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [this, mul_one]

end P99bcb804

end X6_Cg2

section X7_Cg3

/-! R4 / Q3: hypotheses of `lclt_dens` for the centred tilted law `Hc G t`.
* `smooth_taylor`: Gaussian smoothing keeps a cubic Taylor bound of `charFun`;
* `Hc G t = (G.tilted (t·)).map (· - tmu G t)`: `Hc_prob`, `int_Hc`, `Hc_mean`, `Hc_var`;
* `Hc_m3`: uniform third absolute moment on `|t| ≤ t1`;
* `Hc_far`: `‖charFun (Hc G t) s · e^{-σ²s²/2}‖ ≤ 1 - (p/2)(1-e^{-v/2}) min(s²,1)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma smooth_taylor (χ0 : ℂ) {V σ s B3 : ℝ} (hV0 : 0 ≤ V) (hV : V ≤ 2) (hσ1 : σ ^ 2 ≤ 1)
    (h : ‖χ0 - (1 - V * s ^ 2 / 2)‖ ≤ 4 * B3 * |s| ^ 3) :
    ‖χ0 * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ) - (1 - (V + σ ^ 2) * s ^ 2 / 2)‖
      ≤ (4 * B3 + 5) * |s| ^ 3 := by
  set u := σ ^ 2 / 2 * s ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  set e := exp (-(σ ^ 2 / 2) * s ^ 2) with he
  have he' : e = exp (-u) := by rw [he, hu]; ring_nf
  have he0 : 0 < e := exp_pos _
  have he1 : e ≤ 1 := by rw [he']; exact exp_le_one_iff.2 (by linarith)
  have split : χ0 * (e : ℂ) - (1 - (V + σ ^ 2) * s ^ 2 / 2)
      = (χ0 - (1 - V * s ^ 2 / 2)) * (e : ℂ)
        + (((1 - V * s ^ 2 / 2) * e - (1 - V * s ^ 2 / 2 - u) : ℝ) : ℂ) := by
    rw [hu]; push_cast; ring
  rw [split]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he0, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 : ‖χ0 - (1 - V * s ^ 2 / 2)‖ * e ≤ 4 * B3 * |s| ^ 3 := by
    calc _ ≤ ‖χ0 - (1 - V * s ^ 2 / 2)‖ * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact h
  set a := |s| with ha
  have ha0 : 0 ≤ a := abs_nonneg s
  have hs2 : s ^ 2 = a ^ 2 := (sq_abs s).symm
  have huu : u ≤ a ^ 2 / 2 := by rw [hu, hs2]; nlinarith [sq_nonneg a]
  have h2 : |(1 - V * s ^ 2 / 2) * e - (1 - V * s ^ 2 / 2 - u)| ≤ 5 * a ^ 3 := by
    rw [hs2]
    rcases le_or_gt a 1 with hs | hs
    · have hu1 : u ≤ 1 := by nlinarith
      have hq := exp_neg_quad hu0 hu1
      have eq : (1 - V * a ^ 2 / 2) * e - (1 - V * a ^ 2 / 2 - u)
          = (1 - V * a ^ 2 / 2) * (exp (-u) - (1 - u)) + V * a ^ 2 / 2 * u := by
        rw [he']; ring
      rw [eq]
      have ha2 : a ^ 2 ≤ 1 := by nlinarith
      have hVa2 : V * a ^ 2 ≤ 2 := by nlinarith [mul_le_mul hV ha2 (sq_nonneg a) (by norm_num)]
      have hVa0 : 0 ≤ V * a ^ 2 := by positivity
      have hab : |1 - V * a ^ 2 / 2| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
      have ha4 : a ^ 4 ≤ a ^ 3 := by
        have : a ^ 4 = a ^ 3 * a := by ring
        rw [this]; nlinarith [pow_nonneg ha0 3]
      have hu2 : u ^ 2 ≤ a ^ 3 / 4 := by nlinarith
      have hVu : V * a ^ 2 / 2 * u ≤ a ^ 3 / 2 := by nlinarith
      have hVu0 : 0 ≤ V * a ^ 2 / 2 * u := by positivity
      calc |(1 - V * a ^ 2 / 2) * (exp (-u) - (1 - u)) + V * a ^ 2 / 2 * u|
          ≤ |1 - V * a ^ 2 / 2| * |exp (-u) - (1 - u)| + V * a ^ 2 / 2 * u := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hVu0]
        _ ≤ 2 * u ^ 2 + a ^ 3 / 2 := by gcongr
        _ ≤ 5 * a ^ 3 := by nlinarith [pow_nonneg ha0 3]
    · have ha3 : a ^ 2 ≤ a ^ 3 := by
        have : a ^ 3 = a ^ 2 * a := by ring
        rw [this]; nlinarith [sq_nonneg a]
      have h13 : 1 ≤ a ^ 3 := one_le_pow₀ hs.le
      have hVa : 0 ≤ V * a ^ 2 / 2 := by positivity
      calc |(1 - V * a ^ 2 / 2) * e - (1 - V * a ^ 2 / 2 - u)|
          ≤ |1 - V * a ^ 2 / 2| * e + |1 - V * a ^ 2 / 2 - u| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_of_pos he0]
        _ ≤ (1 + a ^ 2) * 1 + (1 + a ^ 2 + a ^ 2 / 2) := by
            gcongr
            · exact (abs_sub _ _).trans (by rw [abs_one, abs_of_nonneg hVa]; nlinarith)
            · refine (abs_sub _ _).trans ?_
              rw [abs_of_nonneg hu0]
              have := (abs_sub (1 : ℝ) (V * a ^ 2 / 2))
              rw [abs_one, abs_of_nonneg hVa] at this
              nlinarith
        _ ≤ 5 * a ^ 3 := by nlinarith
  calc _ ≤ 4 * B3 * a ^ 3 + 5 * a ^ 3 := add_le_add h1 h2
    _ = _ := by ring

section Hc

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

/-- The tilted mean `ψ'(t)`. -/
noncomputable def tmu (G : Measure ℝ) (t : ℝ) : ℝ := deriv (cgf (fun x : ℝ => x) G) t

/-- The centred tilted law. -/
noncomputable def Hc (G : Measure ℝ) (t : ℝ) : Measure ℝ :=
  (G.tilted (fun x => t * x)).map (fun x => x - tmu G t)

lemma Hc_prob (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| ≤ a0) : IsProbabilityMeasure (Hc G t) := by
  have : IsProbabilityMeasure (G.tilted (fun x => t * x)) := isProbabilityMeasure_tilted (hexp t ht)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma int_Hc (t : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ y, g y ∂(Hc G t) = ∫ x, g (x - tmu G t) ∂(G.tilted (fun x => t * x)) :=
  integral_map (measurable_sub_const _).aemeasurable hg.aestronglyMeasurable

lemma mem_int_of (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| < a0) : t ∈ interior (integrableExpSet (fun x : ℝ => x) G) :=
  ioo_sub_int hexp ⟨by linarith [(abs_lt.1 ht).1], (abs_lt.1 ht).2⟩

lemma Hc_mean (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| < a0) : ∫ y, y ∂(Hc G t) = 0 := by
  have hin := mem_int_of hexp ht
  have : IsProbabilityMeasure (G.tilted (fun x => t * x)) :=
    isProbabilityMeasure_tilted (hexp t ht.le)
  have hL := memLp_tilted_mul hin 1
  rw [ENNReal.coe_one, memLp_one_iff_integrable] at hL
  have hm := integral_tilted_mul_self hin
  rw [int_Hc t (fun y => y) continuous_id, integral_sub hL (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul]
  rw [tmu, ← hm]
  simp

lemma Hc_var (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| < a0) :
    ∫ y, y ^ 2 ∂(Hc G t) = iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t := by
  have hin := mem_int_of hexp ht
  have hv := variance_tilted_mul hin
  rw [variance_eq_integral (by fun_prop), integral_tilted_mul_self hin] at hv
  rw [int_Hc t (fun y => y ^ 2) (by fun_prop), tmu, ← hv]

end Hc

end P99bcb804

end X7_Cg3

section X8_Cg4

/-! R4 / Q3: uniform third moment and the far bound for `Hc G t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma cube_le (a b : ℝ) : |a - b| ^ 3 ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
  have h := abs_sub a b
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  calc |a - b| ^ 3 ≤ (|a| + |b|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h 3
    _ ≤ 4 * (|a| ^ 3 + |b| ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (|a| - |b|))]

lemma exp_le_two_side {t t1 x : ℝ} (ht : |t| ≤ t1) :
    exp (t * x) ≤ exp (t1 * x) + exp (-t1 * x) := by
  have h : t * x ≤ t1 * |x| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right ht (abs_nonneg x))
  have p1 := exp_pos (t1 * x)
  have p2 := exp_pos (-t1 * x)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h
    linarith [exp_le_exp.2 h]
  · rw [abs_of_nonpos hx] at h
    have : t * x ≤ -t1 * x := by linarith
    linarith [exp_le_exp.2 this]

section Hc2

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma Hc_m3 (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) :
    ∃ B3 : ℝ, 0 ≤ B3 ∧ ∀ t : ℝ, |t| ≤ t1 →
      Integrable (fun y : ℝ => |y| ^ 3) (Hc G t) ∧ ∫ y, |y| ^ 3 ∂(Hc G t) ≤ B3 := by
  have hsub : Icc (-t1) t1 ⊆ interior (integrableExpSet (fun x : ℝ => x) G) := fun x hx =>
    ioo_sub_int hexp ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨tm, htm, hmin⟩ := (isCompact_Icc (a := -t1) (b := t1)).exists_isMinOn
    (nonempty_Icc.2 (by linarith)) (continuousOn_mgf.mono hsub)
  set c := mgf (fun x : ℝ => x) G tm with hcdef
  have hc : 0 < c := mgf_pos (hexp tm (abs_le.2 ⟨by linarith [htm.1], by linarith [htm.2]⟩))
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -t1) (b := t1)).exists_bound_of_continuousOn
    ((an_cgf hexp 1).continuousOn.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  set Km := max K 0 with hKm
  have hKm0 : 0 ≤ Km := le_max_right _ _
  set E : ℝ → ℝ := fun x => exp (t1 * x) + exp (-t1 * x) with hEdef
  have hE0 : ∀ x, 0 ≤ E x := fun x => by rw [hEdef]; positivity
  have hE : Integrable E G :=
    (hexp t1 (by rw [abs_of_pos ht1]; linarith)).add
      (hexp (-t1) (by rw [abs_neg, abs_of_pos ht1]; linarith))
  have hE3 : Integrable (fun x => |x| ^ 3 * E x) G := by
    have i1 := integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
      (hsub ⟨by linarith, le_rfl⟩) 3
    have i2 := integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
      (hsub ⟨le_rfl, by linarith⟩) 3
    simp only [hEdef, mul_add]
    exact i1.add i2
  set B3 := 4 / c * (∫ x, |x| ^ 3 * E x ∂G + Km ^ 3 * ∫ x, E x ∂G) with hB3
  have hint0 : 0 ≤ ∫ x, |x| ^ 3 * E x ∂G :=
    integral_nonneg fun x => mul_nonneg (pow_nonneg (abs_nonneg x) 3) (hE0 x)
  have hint1 : 0 ≤ ∫ x, E x ∂G := integral_nonneg hE0
  refine ⟨B3, by positivity, fun t ht => ?_⟩
  have htI : t ∈ Icc (-t1) t1 := ⟨by linarith [(abs_le.1 ht).1], (abs_le.1 ht).2⟩
  have hI : Integrable (fun x : ℝ => exp (t * x)) G := hexp t (by linarith)
  set M := mgf (fun x : ℝ => x) G t with hMdef
  have hcM : c ≤ M := hmin htI
  set μt := tmu G t with hμt
  have hμK : |μt| ≤ Km := by
    have := hK t htI
    rw [Real.norm_eq_abs, iteratedDeriv_one] at this
    exact this.trans (le_max_left _ _)
  have hpt : ∀ x : ℝ, |x - μt| ^ 3 ≤ 4 * (|x| ^ 3 + Km ^ 3) := by
    intro x
    refine (cube_le x μt).trans ?_
    gcongr
  have hpos : ∀ x : ℝ, 0 ≤ exp (t * x) * |x - μt| ^ 3 := fun x => by positivity
  have hbd : ∀ x : ℝ, exp (t * x) * |x - μt| ^ 3 ≤ 4 * (|x| ^ 3 * E x + Km ^ 3 * E x) := by
    intro x
    calc exp (t * x) * |x - μt| ^ 3 ≤ E x * (4 * (|x| ^ 3 + Km ^ 3)) :=
          mul_le_mul (exp_le_two_side ht) (hpt x) (by positivity) (hE0 x)
      _ = _ := by ring
  have hR : Integrable (fun x => 4 * (|x| ^ 3 * E x + Km ^ 3 * E x)) G :=
    (hE3.add (hE.const_mul _)).const_mul 4
  have hL : Integrable (fun x => exp (t * x) * |x - μt| ^ 3) G :=
    hR.mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos x)]; exact hbd x)
  have hmeas : AEStronglyMeasurable (fun y : ℝ => |y| ^ 3) (Hc G t) := by fun_prop
  constructor
  · rw [Hc, integrable_map_measure (by fun_prop) (measurable_sub_const _).aemeasurable]
    · rw [integrable_tilted_iff hI]
      simpa [Function.comp_apply, smul_eq_mul] using hL
  · rw [int_Hc t (fun y => |y| ^ 3) (by fun_prop), integral_tilted]
    have hMpos : 0 < M := lt_of_lt_of_le hc hcM
    calc ∫ x, (exp (t * x) / ∫ x, exp (t * x) ∂G) • |x - μt| ^ 3 ∂G
        = (∫ x, exp (t * x) * |x - μt| ^ 3 ∂G) / M := by
          rw [← integral_div]
          congr 1; funext x
          rw [smul_eq_mul, hMdef, mgf]
          ring
      _ ≤ (∫ x, 4 * (|x| ^ 3 * E x + Km ^ 3 * E x) ∂G) / c := by
          have h1 : ∫ x, exp (t * x) * |x - μt| ^ 3 ∂G
              ≤ ∫ x, 4 * (|x| ^ 3 * E x + Km ^ 3 * E x) ∂G :=
            integral_mono_of_nonneg (Eventually.of_forall hpos) hR (Eventually.of_forall hbd)
          have h0 : 0 ≤ ∫ x, exp (t * x) * |x - μt| ^ 3 ∂G := integral_nonneg hpos
          calc _ ≤ (∫ x, exp (t * x) * |x - μt| ^ 3 ∂G) / c := by gcongr
            _ ≤ _ := by gcongr
      _ = B3 := by
          rw [integral_const_mul, integral_add hE3 (hE.const_mul _), integral_const_mul, hB3]
          ring

lemma Hc_far (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2) {t : ℝ}
    (hI : Integrable (fun x : ℝ => exp (t * x)) G)
    (hpt : 1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t)
    (σ s : ℝ) :
    ‖charFun (Hc G t) s * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ)‖
      ≤ 1 - p / 2 * (1 - exp (-((v : ℝ) / 2))) * min (s ^ 2) 1 := by
  have hk : 0 ≤ (1 - exp (-((v : ℝ) / 2))) * min (s ^ 2) 1 :=
    mul_nonneg (by have : exp (-((v : ℝ) / 2)) ≤ 1 := exp_le_one_iff.2 (by
      have : (0 : ℝ) ≤ v := v.2; linarith); linarith) (le_min (sq_nonneg _) zero_le_one)
  have hk1 : (1 - exp (-((v : ℝ) / 2))) * min (s ^ 2) 1 ≤ 1 := by
    have e1 : 1 - exp (-((v : ℝ) / 2)) ≤ 1 := by linarith [exp_pos (-((v : ℝ) / 2))]
    have e2 : min (s ^ 2) 1 ≤ 1 := min_le_right _ _
    have e3 : 0 ≤ min (s ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    nlinarith
  have h1 : ‖charFun (Hc G t) s‖ ≤ 1 - p / 2 * (1 - exp (-((v : ℝ) / 2))) * min (s ^ 2) 1 := by
    rw [Hc, norm_cf_shift]
    subst hG
    refine (norm_cf_tilt_mix p hp0 hp1 m v F2 t s hI).trans ?_
    set q := mgf (fun x : ℝ => x) (gaussianReal m v) t
      / mgf (fun x : ℝ => x) (ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2) t
      with hq
    have hq0 : 0 ≤ q := by linarith
    rw [mul_div_assoc, ← hq]
    have := gmix_far (p := p * q) (a := (v : ℝ) / 2) (mul_nonneg hp0 hq0) (by positivity) s
    refine this.trans ?_
    have : p / 2 ≤ p * q := by nlinarith
    nlinarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have he1 : exp (-(σ ^ 2 / 2) * s ^ 2) ≤ 1 :=
    exp_le_one_iff.2 (by nlinarith [sq_nonneg σ, sq_nonneg s])
  calc ‖charFun (Hc G t) s‖ * exp (-(σ ^ 2 / 2) * s ^ 2) ≤ ‖charFun (Hc G t) s‖ * 1 := by
        gcongr
    _ ≤ _ := by rw [mul_one]; exact h1

end Hc2

end P99bcb804

end X8_Cg4

section X9_Cr1

/-! R4 / Cr1: local CLT for the smoothed iid-sum density at ANY small tilt `t`.
`lc_any`: for `G = p N(m,v) + (1-p) F2` (exp moments, mean 0, var 1), uniformly in `|t| ≤ t1`, `σ ∈ (0,1]`, `N ≥ 2`:
`f(a) = M^N e^{t²Nσ²/2} e^{-ta} (φ_{N(V_t+σ²)}(a - tNσ² - N μ_t) ± (C/N + C(1-κ')^{N-1}/σ))`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Cr1

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma cr_inner {ι : Type} [Fintype ι] (G : Measure ℝ) (t : ℝ)
    [IsProbabilityMeasure (G.tilted (fun x => t * x))] (w : ℝ≥0) (b : ℝ) :
    ∫ y, gaussianPDFReal 0 w (b - y)
        ∂((Measure.pi fun _ : ι => G.tilted (fun x => t * x)).map (fun p => ∑ i, p i))
      = ∫ y, gaussianPDFReal 0 w (b - Fintype.card ι * tmu G t - y)
        ∂((Measure.pi fun _ : ι => Hc G t).map (fun p => ∑ i, p i)) := by
  rw [Hc, sum_center, integral_map (φ := fun y => y - (Fintype.card ι : ℝ) * tmu G t)
    (by fun_prop) ?_]
  swap
  · exact ((measurable_gaussianPDFReal 0 w).comp (measurable_const_sub _)).aestronglyMeasurable
  congr 1
  funext y
  congr 1
  ring

lemma cr_comb (K X Y Z E : ℝ) (hX : X = K * Y) (hE : |Y - Z| ≤ E) (hK : 0 ≤ K) :
    |X - K * Z| ≤ K * E := by
  rw [hX, ← mul_sub, abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left hE hK

set_option maxHeartbeats 400000 in
theorem lc_any (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ C κ' : ℝ, 0 < C ∧ 0 < κ' ∧ κ' ≤ 1 ∧
      ∀ (ι : Type) [Fintype ι] (t σ a : ℝ), |t| ≤ t1 → 0 < σ → σ ≤ 1 → 2 ≤ Fintype.card ι →
        |(∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
              ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i)))
            - mgf (fun x : ℝ => x) G t ^ Fintype.card ι
              * exp (t ^ 2 * (Fintype.card ι * σ ^ 2) / 2) * exp (-(t * a)) *
              gaussianPDFReal 0
                (Fintype.card ι * (iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2)).toNNReal
                (a - t * (Fintype.card ι * σ ^ 2) - Fintype.card ι * tmu G t)|
          ≤ mgf (fun x : ℝ => x) G t ^ Fintype.card ι
              * exp (t ^ 2 * (Fintype.card ι * σ ^ 2) / 2) * exp (-(t * a)) *
              (C / Fintype.card ι + C * (1 - κ') ^ (Fintype.card ι - 1) / σ) := by
  obtain ⟨B3, hB30, hB3⟩ := Hc_m3 hexp ht1 h2
  set κ := p / 2 * (1 - exp (-((v : ℝ) / 2))) with hκ
  have hvpos : (0 : ℝ) < v := hv0
  have hel : exp (-((v : ℝ) / 2)) < 1 := exp_lt_one_iff.2 (by linarith)
  have hep : 0 < exp (-((v : ℝ) / 2)) := exp_pos _
  have hκ0 : 0 < κ := by
    have : 0 < 1 - exp (-((v : ℝ) / 2)) := by linarith
    positivity
  have hκ1 : κ ≤ 1 := by
    have h1 : 1 - exp (-((v : ℝ) / 2)) ≤ 1 := by linarith
    have h2 : p / 2 ≤ 1 := by linarith
    have h3 : 0 ≤ 1 - exp (-((v : ℝ) / 2)) := by linarith
    rw [hκ]; exact mul_le_one₀ h2 h3 h1
  obtain ⟨C, κ', hC, hκ'0, hκ'1, H⟩ :=
    lclt_dens κ (4 * B3 + 5) (1 / 2) 3 hκ0 hκ1 (by positivity) (by norm_num) (by norm_num)
  refine ⟨C, κ', hC, hκ'0, hκ'1, ?_⟩
  intro ι _ t σ a ht hσ hσ1 hN
  have hta : |t| < a0 := by linarith
  have hta' : |t| ≤ a0 := hta.le
  have : IsProbabilityMeasure (Hc G t) := Hc_prob hexp hta'
  obtain ⟨hint3, hm3⟩ := hB3 t ht
  obtain ⟨hV1, hV2⟩ := hV t ht
  have hI : Integrable (fun x => exp (t * x)) G := hexp t hta'
  have : IsProbabilityMeasure (G.tilted (fun x => t * x)) := isProbabilityMeasure_tilted hI
  set N := Fintype.card ι with hNdef
  set w : ℝ≥0 := ((N : ℝ) * σ ^ 2).toNNReal with hwdef
  have hw : (w : ℝ) = N * σ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have htd := tilt_dens (ι := ι) G hI w a
  rw [hw] at htd
  have hfar : ∀ s, ‖charFun (Hc G t) s * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ)‖
      ≤ 1 - κ * min (s ^ 2) 1 := fun s =>
    Hc_far p m v F2 hp0.le hp1 hG hI (hpt t ht) σ s
  have htay : ∀ s, ‖charFun (Hc G t) s * ((exp (-(σ ^ 2 / 2) * s ^ 2) : ℝ) : ℂ)
      - (1 - (((iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2 : ℝ)) : ℂ) * s ^ 2 / 2)‖
      ≤ (4 * B3 + 5) * |s| ^ 3 := by
    intro s
    rw [Complex.ofReal_add, Complex.ofReal_pow]
    refine smooth_taylor _ (by linarith) hV2 (pow_le_one₀ hσ.le hσ1) ?_
    have h := charFun_taylor3 (Hc G t) hint3 (Hc_mean hexp hta) s
    rw [Hc_var hexp hta] at h
    refine h.trans ?_
    have : 0 ≤ |s| ^ 3 := by positivity
    have h4 : 4 * (∫ y, |y| ^ 3 ∂(Hc G t)) ≤ 4 * B3 := by linarith
    exact mul_le_mul_of_nonneg_right h4 this
  have hL := H (Hc G t) ι (iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2) σ
    (by have := sq_nonneg σ; linarith) (by have := pow_le_one₀ (n := 2) hσ.le hσ1; linarith) hσ hN hfar htay (a - t * (N * σ ^ 2) - N * tmu G t)
  rw [cr_inner] at htd
  have hM : 0 ≤ mgf (fun x : ℝ => x) G t := mgf_nonneg
  exact cr_comb _ _ _ _ _ htd hL (by positivity)

end Cr1

end P99bcb804

end X9_Cr1

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
        ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
          (0 : ℝ) < p →
            p ≤ (1 : ℝ) →
              (0 : NNReal) < v →
                G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                  ∀ {t1 : ℝ},
                    (0 : ℝ) < t1 →
                      (2 : ℝ) * t1 < a0 →
                        (∀ (t : ℝ),
                            |t| ≤ t1 →
                              (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                          (∀ (t : ℝ),
                              |t| ≤ t1 →
                                (1 / 2 : ℝ) ≤
                                  ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                    ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                            ∃ (C : ℝ) (κ' : ℝ),
                              (0 : ℝ) < C ∧
                                (0 : ℝ) < κ' ∧
                                  κ' ≤ (1 : ℝ) ∧
                                    ∀ (ι : Type) [inst : Fintype ι] (t σ a : ℝ),
                                      |t| ≤ t1 →
                                        (0 : ℝ) < σ →
                                          σ ≤ (1 : ℝ) →
                                            (2 : ℕ) ≤ Fintype.card ι →
                                              |∫ (y : ℝ),
                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                        (Real.toNNReal (↑(Fintype.card ι) * σ ^ (2 : ℕ)))
                                                        (a -
                                                          y) ∂MeasureTheory.Measure.map (fun (p : ι → ℝ) => ∑ i : ι, p i)
                                                        (MeasureTheory.Measure.pi fun (x : ι) => G) -
                                                    ProbabilityTheory.mgf (fun (x : ℝ) => x) G t ^ Fintype.card ι *
                                                          Real.exp
                                                            (t ^ (2 : ℕ) * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) / (2 : ℝ)) *
                                                        Real.exp (-(t * a)) *
                                                      ProbabilityTheory.gaussianPDFReal (0 : ℝ)
                                                        (Real.toNNReal
                                                          (↑(Fintype.card ι) *
                                                            (iteratedDeriv (2 : ℕ)
                                                                (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t +
                                                              σ ^ (2 : ℕ))))
                                                        (a - t * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) -
                                                          ↑(Fintype.card ι) *
                                                            deriv (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t)| ≤
                                                ProbabilityTheory.mgf (fun (x : ℝ) => x) G t ^ Fintype.card ι *
                                                      Real.exp (t ^ (2 : ℕ) * (↑(Fintype.card ι) * σ ^ (2 : ℕ)) / (2 : ℝ)) *
                                                    Real.exp (-(t * a)) *
                                                  (C / ↑(Fintype.card ι) +
                                                    C * ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ) := by
  first
  | exact P99bcb804.lc_any
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.lc_any <;> assumption)
