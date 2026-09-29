-- Prove2me | solution 1 for BanditAlgorithm.tendsto_chernoffInverse_div_log
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T20:03:40.890415+00:00
-- url     : https://prove2.me/submissions/ed36db40-9f9d-4163-a96b-b6605b072a09

import Definitions.Def_TrackAndStop


/-!
# Chernoff's stopping rule: threshold arithmetic and the stopping-time property

This file establishes the two *structural* clauses of L&S Lemma 33.7 — everything
about `τ_δ` and `ψ_δ` except the probability bound itself:

* `chernoffInverse_ge`, `chernoffThreshold_pos` — the threshold `β_t(δ)` is
  strictly positive.  This is what forces the empirical maximiser to be unique
  whenever the learner stops, which is in turn what makes the recommendation
  measurable at all (`chernoffRecommendation` is built from the `Classical.choose`
  maximiser `trajEmpiricalBestArm`).
* `isBanditStoppingTime_chernoffStoppingTime` — `τ_δ` is a stopping time of the
  natural filtration.
* `measurable_chernoffRecommendation` — `ψ_δ` is `𝓕_{τ_δ}`-measurable.

The positivity argument is the one implicit in L&S p. 410: `f⁻¹(δ)` is the least
`x ≥ k` with `f(x) ≤ δ`, so `f⁻¹(δ) ≥ k ≥ 1` as soon as that set is nonempty —
which it is, because `f(x) = e^{k-x}(x/k)^k → 0` as `x → ∞`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The Chernoff function and its inverse -/

/-- `f(k) = 1`. -/
theorem chernoffF_self (hk : 0 < k) : chernoffF k (k : ℝ) = 1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [chernoffF, div_self hk']

/-- `f(x) = e^{k-x}(x/k)^k` tends to `0` as `x → ∞`. -/
theorem tendsto_chernoffF (hk : 0 < k) :
    Tendsto (chernoffF k) atTop (nhds 0) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hrw : chernoffF k = fun x : ℝ ↦
      (Real.exp (k : ℝ) / ((k : ℝ) ^ k)) * (x ^ k * Real.exp (-x)) := by
    funext x
    rw [chernoffF, div_pow, sub_eq_add_neg, Real.exp_add]
    field_simp
  rw [hrw]
  simpa using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero k)

/-- The set defining `f⁻¹(δ)` is nonempty for every `δ > 0`. -/
theorem chernoffInverse_set_nonempty (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}.Nonempty := by
  have h1 : ∀ᶠ x : ℝ in atTop, chernoffF k x ≤ δ :=
    (tendsto_chernoffF hk).eventually (eventually_le_nhds hδ)
  have h2 : ∀ᶠ x : ℝ in atTop, (k : ℝ) ≤ x := eventually_ge_atTop _
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  exact ⟨x, hx2, hx1⟩

theorem chernoffInverse_set_bddBelow {δ : ℝ} :
    BddBelow {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  ⟨(k : ℝ), fun _ hx ↦ hx.1⟩

/-- `f⁻¹(δ) ≥ k`. -/
theorem chernoffInverse_ge (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ :=
  le_csInf (chernoffInverse_set_nonempty hk hδ) fun _ hx ↦ hx.1

/-- `f⁻¹(δ) > 0`. -/
theorem chernoffInverse_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (chernoffInverse_ge hk hδ)

/-- The threshold `β_t(δ) = k log(t² + t) + f⁻¹(δ)` is strictly positive. -/
theorem chernoffThreshold_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    0 < chernoffThreshold k δ t := by
  have hlog : 0 ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ)) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · norm_num
    · refine mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg ?_)
      have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      nlinarith
  have hinv := chernoffInverse_pos hk hδ
  rw [chernoffThreshold]
  linarith


end BanditAlgorithm



/-!
# The Chernoff inverse `f⁻¹(δ)`

`f(x) = e^{k−x}(x/k)^k` is continuous, equal to `1` at `x = k`, strictly
decreasing on `[k, ∞)`, and tends to `0`.  `chernoffInverse k δ` is defined as the
infimum of `{x ≥ k : f(x) ≤ δ}`, and this file proves the facts that make that
definition behave like an inverse:

* `chernoffF_chernoffInverse_le` — the infimum is attained, so `f(f⁻¹(δ)) ≤ δ`.
  This is what the soundness proof of L&S Lemma 33.7 actually consumes: the
  threshold really does deliver the promised confidence level.
* `chernoffInverse_le_of_le` — any admissible `x` bounds `f⁻¹(δ)` from above, so
  explicit thresholds can be plugged in.
* `chernoffInverse_antitone` — smaller confidence level, larger threshold.
* `chernoffF_antitoneOn` — `f` is decreasing on `[k, ∞)`, which is what makes
  `f⁻¹` an inverse rather than merely a lower bound.

Together with `chernoffThreshold_pos` these are all the properties of `β_t(δ)`
used anywhere in the Track-and-Stop analysis.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real Set

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Continuity and monotonicity of `f` -/

theorem continuous_chernoffF (k : ℕ) : Continuous (chernoffF k) := by
  unfold chernoffF
  fun_prop

/-- `f` is strictly decreasing on `[k, ∞)`: its logarithmic derivative is
`k/x − 1 < 0` there.  We prove the (equivalent, and sufficient) statement that
`f` is antitone on `[k, ∞)` directly from `log x ≤ x − 1`. -/
theorem chernoffF_le_chernoffF_of_le (hk : 0 < k) {x y : ℝ} (hx : (k : ℝ) ≤ x)
    (hxy : x ≤ y) : chernoffF k y ≤ chernoffF k x := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hkR hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
  -- compare logarithms
  have hlog : Real.log (chernoffF k y) ≤ Real.log (chernoffF k x) := by
    have hlx : Real.log (chernoffF k x)
        = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hx0.ne' hkR.ne']
    have hly : Real.log (chernoffF k y)
        = ((k : ℝ) - y) + k * (Real.log y - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hy0.ne' hkR.ne']
    rw [hlx, hly]
    -- `k (log y − log x) ≤ y − x` because `log(y/x) ≤ y/x − 1` and `x ≥ k`
    have hratio : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hy0.ne' hx0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hkx : (k : ℝ) * (y / x - 1) ≤ y - x := by
      have hyx : 0 ≤ y / x - 1 := by
        rw [sub_nonneg, le_div_iff₀ hx0]
        linarith
      calc (k : ℝ) * (y / x - 1) ≤ x * (y / x - 1) := by
            exact mul_le_mul_of_nonneg_right (le_trans hx (le_refl x)) hyx
        _ = y - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hratio (le_of_lt hkR)]
  have hposx : 0 < chernoffF k x := by
    rw [chernoffF]; positivity
  have hposy : 0 < chernoffF k y := by
    rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hposy hposx).mp hlog

/-! ## 2. The infimum is attained -/

theorem isClosed_chernoffInverse_set (k : ℕ) (δ : ℝ) :
    IsClosed {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} := by
  have h : {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}
      = Set.Ici (k : ℝ) ∩ chernoffF k ⁻¹' Set.Iic δ := by
    ext x; simp [and_comm]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Iic.preimage (continuous_chernoffF k))

/-- **The infimum defining `f⁻¹(δ)` is attained.** -/
theorem chernoffInverse_mem (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffInverse k δ ∈ {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  IsClosed.csInf_mem (isClosed_chernoffInverse_set k δ)
    (chernoffInverse_set_nonempty hk hδ) chernoffInverse_set_bddBelow

/-- **`f⁻¹(δ)` really is a threshold at confidence `δ`.** -/
theorem chernoffF_chernoffInverse_le (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffF k (chernoffInverse k δ) ≤ δ :=
  (chernoffInverse_mem hk hδ).2

/-- Above the threshold the Chernoff function stays below `δ`. -/
theorem chernoffF_le_of_chernoffInverse_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ)
    (hx : chernoffInverse k δ ≤ x) : chernoffF k x ≤ δ :=
  le_trans (chernoffF_le_chernoffF_of_le hk (chernoffInverse_mem hk hδ).1 hx)
    (chernoffF_chernoffInverse_le hk hδ)

/-! ## 3. Comparison -/

/-- Any admissible point bounds the threshold. -/
theorem chernoffInverse_le_of_le {δ x : ℝ} (hx : (k : ℝ) ≤ x) (hfx : chernoffF k x ≤ δ) :
    chernoffInverse k δ ≤ x :=
  csInf_le chernoffInverse_set_bddBelow ⟨hx, hfx⟩

/-- Smaller confidence level, larger threshold. -/
theorem chernoffInverse_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ') :
    chernoffInverse k δ' ≤ chernoffInverse k δ :=
  chernoffInverse_le_of_le (chernoffInverse_mem hk hδ).1
    (le_trans (chernoffF_chernoffInverse_le hk hδ) h)

/-- The threshold is `k` exactly at confidence level `1`, and at least `k`
always. -/
theorem chernoffInverse_one (hk : 0 < k) : chernoffInverse k 1 = (k : ℝ) :=
  le_antisymm (chernoffInverse_le_of_le le_rfl (le_of_eq (chernoffF_self hk)))
    (chernoffInverse_ge hk one_pos)

/-! ## 4. Monotonicity of the whole threshold -/

theorem chernoffThreshold_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ')
    (t : ℕ) : chernoffThreshold k δ' t ≤ chernoffThreshold k δ t := by
  unfold chernoffThreshold
  exact add_le_add_right (chernoffInverse_antitone hk hδ h) _

end BanditAlgorithm



/-!
# An explicit `O(log(1/δ))` bound on the Chernoff inverse

L&S use `f⁻¹(δ) = (1 + o(1)) log(1/δ)` to keep the leading constant of
Theorem 33.6 exact.  The `o(1)` is delicate, but the *order* is elementary and is
what every finiteness argument needs:

  `f⁻¹(δ) ≤ (k + log(1/δ)) / (1 − 1/e)`.

The proof is one application of `log y ≤ y/e` (itself `log(y/e) ≤ y/e − 1`):

  `log f(x) = (k − x) + k log(x/k) ≤ (k − x) + x/e = k − x(1 − 1/e)`,

so `f(x) ≤ δ` as soon as `x (1 − 1/e) ≥ k + log(1/δ)`; and any such `x` is
automatically `≥ k`, because `1 − 1/e < 1` and `log(1/δ) ≥ 0` for `δ ≤ 1`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `log y ≤ y / e`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := y / Real.exp 1)
    (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- The explicit form of `log f(x)` for `x > 0`. -/
theorem log_chernoffF (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    Real.log (chernoffF k x) = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_div hx.ne' hkR.ne']

/-- **The order bound.**  Every `x` with `x (1 − 1/e) ≥ k + log(1/δ)` is an
admissible threshold. -/
theorem chernoffF_le_of_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : (k : ℝ) + Real.log (1 / δ) ≤ x * (1 - (Real.exp 1)⁻¹)) :
    chernoffF k x ≤ δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  have hx0 : 0 < x := by
    by_contra hcon
    push_neg at hcon
    have : x * (1 - (Real.exp 1)⁻¹) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hfac.le
    linarith
  -- the key logarithmic estimate
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ := by
    rw [log_chernoffF hk hx0]
    have hbound : (k : ℝ) * (Real.log x - Real.log k) ≤ x * (Real.exp 1)⁻¹ := by
      have h := log_le_div_exp_one (y := x / (k : ℝ)) (by positivity)
      rw [Real.log_div hx0.ne' hkR.ne'] at h
      calc (k : ℝ) * (Real.log x - Real.log k) ≤ (k : ℝ) * (x / (k : ℝ) / Real.exp 1) :=
            mul_le_mul_of_nonneg_left h hkR.le
        _ = x * (Real.exp 1)⁻¹ := by field_simp
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    rw [hδlog] at hx
    nlinarith
  have hpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hpos hδ).mp hlog

/-- **`f⁻¹(δ) = O(k + log(1/δ))`.** -/
theorem chernoffInverse_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chernoffInverse k δ ≤ ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hfac1 : 1 - (Real.exp 1)⁻¹ ≤ 1 := by
    have : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set x : ℝ := ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) with hxdef
  have hxk : (k : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hfac]
    nlinarith
  refine chernoffInverse_le_of_le hxk (chernoffF_le_of_le hk hδ hδ1 ?_)
  rw [hxdef, div_mul_cancel₀ _ (ne_of_gt hfac)]

/-- Consequently the whole threshold is `O(k log(t²+t) + k + log(1/δ))`. -/
theorem chernoffThreshold_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    chernoffThreshold k δ t
      ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ))
        + ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  rw [chernoffThreshold]
  exact add_le_add_right (chernoffInverse_le_explicit hk hδ hδ1) _

end BanditAlgorithm



/-!
# `f⁻¹(δ) = (1 + o(1)) log(1/δ)`

This is the estimate that keeps the leading constant of L&S Theorem 33.6 *exact*.
The general exponential-family stopping rule (Garivier–Kaufmann Proposition 12)
needs an inflation factor `α > 1` and delivers only `α · c*(ν)`; the Gaussian
threshold `f(x) = e^{k−x}(x/k)^k` of Lemma 33.7 avoids that because its inverse is
asymptotically `log(1/δ)` on the nose.

Both bounds are elementary once written out, with `L = log(1/δ)`:

* **Lower.**  At `x = f⁻¹(δ)` we have `x ≥ k`, hence `log(x/k) ≥ 0`, hence
  `log f(x) = (k − x) + k log(x/k) ≥ k − x`.  Since `f(x) ≤ δ` this gives
  `k − x ≤ −L`, i.e. `f⁻¹(δ) ≥ L + k`.
* **Upper.**  `log f((1+ε)L) = C + k log L − (1+ε)L` with `C` independent of `L`,
  and `C + k log L ≤ εL` for large `L` because `log = o(id)`.  So `f((1+ε)L) ≤ δ`
  eventually, and `f⁻¹(δ) ≤ (1+ε)L`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real Asymptotics

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. `C + K log L ≤ ε L` eventually -/

theorem eventually_const_add_mul_log_le (K C ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, C + K * Real.log L ≤ ε * L := by
  have hc : 0 < ε / (2 * (K + 1)) := by positivity
  have hbound : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ (ε / (2 * (K + 1))) * ‖L‖ :=
    Real.isLittleO_log_id_atTop.bound hc
  have hCL : ∀ᶠ L : ℝ in atTop, C ≤ ε / 2 * L := by
    have h := Filter.tendsto_id (α := ℝ) (x := atTop)
    have : Filter.Tendsto (fun L : ℝ ↦ ε / 2 * L) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) h
    exact this.eventually_ge_atTop C
  have hpos : ∀ᶠ L : ℝ in atTop, (0 : ℝ) ≤ L := eventually_ge_atTop 0
  filter_upwards [hbound, hCL, hpos] with L hL hC hL0
  have hlog : K * Real.log L ≤ ε / 2 * L := by
    have h1 : Real.log L ≤ (ε / (2 * (K + 1))) * L := by
      calc Real.log L ≤ ‖Real.log L‖ := le_abs_self _
        _ ≤ (ε / (2 * (K + 1))) * ‖L‖ := hL
        _ = (ε / (2 * (K + 1))) * L := by rw [Real.norm_of_nonneg hL0]
    have hK1 : (0 : ℝ) < K + 1 := by linarith
    calc K * Real.log L ≤ K * ((ε / (2 * (K + 1))) * L) := by
          exact mul_le_mul_of_nonneg_left h1 hK
      _ ≤ ε / 2 * L := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hL0
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  linarith

/-! ## 2. The lower bound -/

theorem log_le_chernoffInverse (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log (1 / δ) ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hxk, hfx⟩ := chernoffInverse_mem hk hδ
  set x : ℝ := chernoffInverse k δ with hxdef
  have hx0 : 0 < x := lt_of_lt_of_le hkR hxk
  have hfpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ :=
    Real.log_le_log hfpos hfx
  rw [log_chernoffF hk hx0] at hlog
  have hlogx : Real.log (k : ℝ) ≤ Real.log x := Real.log_le_log hkR hxk
  have hδlog : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  nlinarith

/-! ## 3. The upper bound -/

theorem eventually_chernoffInverse_le (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      chernoffInverse k δ ≤ (1 + ε) * Real.log (1 / δ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hLtop : Tendsto (fun δ : ℝ ↦ Real.log (1 / δ)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have h : Tendsto (fun δ : ℝ ↦ -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    refine h.congr fun δ ↦ ?_
    rw [one_div, Real.log_inv]
  -- the deterministic estimate, in the variable `L`
  set C : ℝ := (k : ℝ) + (k : ℝ) * Real.log (1 + ε) - (k : ℝ) * Real.log (k : ℝ) with hC
  have haux : ∀ᶠ L : ℝ in atTop, C + (k : ℝ) * Real.log L ≤ ε * L :=
    eventually_const_add_mul_log_le (k : ℝ) C ε hkR.le hε
  have hbig : ∀ᶠ L : ℝ in atTop, (k : ℝ) ≤ (1 + ε) * L := by
    have h : Tendsto (fun L : ℝ ↦ (1 + ε) * L) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) tendsto_id
    exact h.eventually_ge_atTop _
  have hLpos : ∀ᶠ L : ℝ in atTop, (0 : ℝ) < L := eventually_gt_atTop 0
  have hmain : ∀ᶠ L : ℝ in atTop,
      Real.log (chernoffF k ((1 + ε) * L)) ≤ -L := by
    filter_upwards [haux, hbig, hLpos] with L hL hbg hLp
    have hxpos : 0 < (1 + ε) * L := by positivity
    rw [log_chernoffF hk hxpos]
    have hsplit : Real.log ((1 + ε) * L) = Real.log (1 + ε) + Real.log L :=
      Real.log_mul (by linarith) (ne_of_gt hLp)
    rw [hsplit]
    rw [hC] at hL
    linarith
  -- transport to `δ`
  filter_upwards [hLtop.eventually hmain, hLtop.eventually hbig,
    hLtop.eventually hLpos, self_mem_nhdsWithin] with δ hlog hbg hLp hδ
  have hδ0 : 0 < δ := hδ
  set L : ℝ := Real.log (1 / δ) with hLdef
  have hδlog : Real.log δ = -L := by rw [hLdef, one_div, Real.log_inv, neg_neg]
  have hxpos : 0 < (1 + ε) * L := by positivity
  have hfpos : 0 < chernoffF k ((1 + ε) * L) := by rw [chernoffF]; positivity
  refine chernoffInverse_le_of_le hbg ?_
  have := (Real.log_le_log_iff hfpos hδ0).mp (by rw [hδlog]; exact hlog)
  exact this

/-! ## 4. The asymptotic -/

/-- **`f⁻¹(δ)/log(1/δ) → 1` as `δ → 0⁺`.** -/
theorem tendsto_chernoffInverse_div_log (hk : 0 < k) :
    Tendsto (fun δ : ℝ ↦ chernoffInverse k δ / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hLtop : Tendsto (fun δ : ℝ ↦ Real.log (1 / δ)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have h : Tendsto (fun δ : ℝ ↦ -Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    refine h.congr fun δ ↦ ?_
    rw [one_div, Real.log_inv]
  have hLpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), (0 : ℝ) < Real.log (1 / δ) :=
    hLtop.eventually (eventually_gt_atTop 0)
  have hδsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ ∈ Set.Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT one_pos
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards [hLpos, hδsmall] with δ hL hδ
    have h1 : Real.log (1 / δ) ≤ chernoffInverse k δ :=
      log_le_chernoffInverse hk hδ.1 hδ.2
    have : (1 : ℝ) ≤ chernoffInverse k δ / Real.log (1 / δ) :=
      (one_le_div hL).mpr h1
    linarith
  · intro b hb
    -- pick `ε` with `1 + ε < b`
    set ε : ℝ := (b - 1) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have hεb : 1 + ε < b := by rw [hεdef]; linarith
    filter_upwards [hLpos, eventually_chernoffInverse_le hk hε] with δ hL hup
    calc chernoffInverse k δ / Real.log (1 / δ)
        ≤ ((1 + ε) * Real.log (1 / δ)) / Real.log (1 / δ) :=
          div_le_div_of_nonneg_right hup hL.le
      _ = 1 + ε := by field_simp
      _ < b := hεb

end BanditAlgorithm


theorem _root_.solution {k : ℕ} (hk : 0 < k) :
    Filter.Tendsto (fun δ : ℝ ↦ BanditAlgorithm.chernoffInverse k δ / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  BanditAlgorithm.tendsto_chernoffInverse_div_log hk
