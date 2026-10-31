-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:22:11.413644+00:00
-- url     : https://prove2.me/submissions/54bc82fc-de41-4b7c-9cda-9fb3b3ef0cb4

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EqExpL2Aux

/-- Bernstein sum `∑_{k ≤ n} C(n,k) μ^k (1-μ)^(n-k) a_k`. -/
noncomputable def bern (n : ℕ) (a : ℕ → ℝ) (μ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) * a k

lemma bern_zero (a : ℕ → ℝ) (μ : ℝ) : bern 0 a μ = a 0 := by
  simp [bern]

lemma bern_succ (n : ℕ) (a : ℕ → ℝ) (μ : ℝ) :
    bern (n + 1) a μ = (1 - μ) * bern n a μ + μ * bern n (fun k => a (k + 1)) μ := by
  unfold bern
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ (k + 1) * (1 - μ) ^ (n + 1 - (k + 1))
      * a (k + 1) = μ * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k)
      * a (k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show n + 1 - (k + 1) = n - k by omega]
    ring
  have h2 : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) * μ ^ (k + 1) *
      (1 - μ) ^ (n + 1 - (k + 1)) * a (k + 1) + (n + 1).choose 0 * μ ^ 0 * (1 - μ) ^ (n + 1 - 0)
      * a 0 = (1 - μ) * ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k)
      * a k := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, zero_mul,
      add_zero]
    conv_rhs => rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n := Finset.mem_range.mp hk
      rw [show n + 1 - (k + 1) = (n - (k + 1)) + 1 by omega, pow_succ]
      ring
    · simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, pow_succ]
      ring
  linarith

lemma bern_mono_seq (n : ℕ) {a b : ℕ → ℝ} (h : ∀ k, a k ≤ b k) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : bern n a μ ≤ bern n b μ := by
  unfold bern
  refine Finset.sum_le_sum fun k _ => ?_
  have : 0 ≤ (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) := by
    have h1 : 0 ≤ 1 - μ := by linarith [hμ.2]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hμ.1 _)) (pow_nonneg h1 _)
  exact mul_le_mul_of_nonneg_left (h k) this

lemma bern_nonneg (n : ℕ) {a : ℕ → ℝ} (h : ∀ k, 0 ≤ a k) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bern n a μ := by
  have := bern_mono_seq n (a := fun _ => 0) (b := a) h hμ
  simpa [bern] using this

lemma bern_antitone (n : ℕ) : ∀ a : ℕ → ℝ, Antitone a → AntitoneOn (bern n a) (Set.Icc 0 1) := by
  induction n with
  | zero =>
    intro a _ x _ y _ _
    simp [bern_zero]
  | succ n ih =>
    intro a ha x hx y hy hxy
    have hS : Antitone (fun k => a (k + 1)) := fun i j hij => ha (by omega)
    rw [bern_succ, bern_succ]
    have e1 := ih a ha hx hy hxy
    have e2 := ih _ hS hx hy hxy
    have e3 : bern n (fun k => a (k + 1)) x ≤ bern n a x :=
      bern_mono_seq n (fun k => ha (Nat.le_succ k)) hx
    have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
    have hy0 : 0 ≤ y := hy.1
    nlinarith [mul_le_mul_of_nonneg_left e1 hy1, mul_le_mul_of_nonneg_left e2 hy0]

lemma bern_continuous (n : ℕ) (a : ℕ → ℝ) : Continuous (bern n a) := by
  unfold bern
  fun_prop



lemma bern_sum_one (n : ℕ) (μ : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) = 1 := by
  have := congrArg (Polynomial.eval μ) (bernsteinPolynomial.sum ℝ n)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_natCast] at this
  exact this

lemma bern_var (n : ℕ) (μ : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) *
      ((k : ℝ) - n * μ) ^ 2 = n * μ * (1 - μ) := by
  have := congrArg (Polynomial.eval μ) (bernsteinPolynomial.variance ℝ n)
  simp only [Polynomial.eval_finsetSum, bernsteinPolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_natCast, nsmul_eq_mul] at this
  rw [← this]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring


open EquilibriumExperiment.Gradient

lemma ae_nonneg_of_Iio (π : Measure ℝ) (hπ : π (Set.Iio 0) = 0) : ∀ᵐ P ∂π, 0 ≤ P := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp [not_le]
  rw [this]; exact hπ

lemma arith_dist {D k n μ d δ η : ℝ} (hk : 0 < k) (hμ : 0 < μ) (hd : 0 < d) (hη : 0 < η)
    (hn : 0 < n) (hDn : |D - n * d| ≤ n * δ) (hk' : |k - n * μ| ≤ n * δ)
    (hkge : n * μ / 2 ≤ k) (hδη : δ ≤ η * μ ^ 2 / (4 * (μ + d))) : |D / k - d / μ| < η := by
  rw [div_sub_div _ _ hk.ne' hμ.ne', abs_div, abs_of_pos (mul_pos hk hμ),
    div_lt_iff₀ (mul_pos hk hμ)]
  have e1 : D * μ - k * d = μ * (D - n * d) - d * (k - n * μ) := by ring
  have e2 : |D * μ - k * d| ≤ μ * (n * δ) + d * (n * δ) := by
    rw [e1]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul, abs_mul, abs_of_pos hμ, abs_of_pos hd]
    exact add_le_add (mul_le_mul_of_nonneg_left hDn hμ.le) (mul_le_mul_of_nonneg_left hk' hd.le)
  have e3 : (μ + d) * δ ≤ η * μ ^ 2 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hδη
    linarith
  have e4 : n * ((μ + d) * δ) ≤ n * (η * μ ^ 2 / 4) := mul_le_mul_of_nonneg_left e3 hn.le
  have e5 : n * μ / 2 * (η * μ) ≤ k * (η * μ) := mul_le_mul_of_nonneg_right hkge (by positivity)
  have e6 : 0 < n * (η * μ ^ 2) := by positivity
  have e7 : μ * (n * δ) + d * (n * δ) = n * ((μ + d) * δ) := by ring
  have e8 : n * μ / 2 * (η * μ) = n * (η * μ ^ 2) / 2 := by ring
  have e9 : k * (η * μ) = η * (k * μ) := by ring
  have e10 : n * (η * μ ^ 2 / 4) = n * (η * μ ^ 2) / 4 := by ring
  linarith

lemma arith_var {Cb ε δ n : ℝ} (hCb : 0 < Cb) (hε : 0 < ε) (hδ : 0 < δ) (hn : 0 < n)
    (h1 : 4 * Cb / (ε * δ ^ 2) < n) : Cb / (n * δ ^ 2) < ε / 4 := by
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [div_lt_iff₀ (by positivity)]
  have : ε * δ ^ 2 * n = ε * (n * δ ^ 2) := by ring
  linarith

lemma sum_bound (n : ℕ) (μ δ A Cb : ℝ) (hn : (0 : ℝ) < n) (hδ : 0 < δ) (hA : 0 ≤ A)
    (hCb : 0 ≤ Cb) (b x : ℕ → ℝ) (hb0 : ∀ k, 0 ≤ b k)
    (hb1 : ∑ k ∈ Finset.range (n + 1), b k = 1)
    (hbv : ∑ k ∈ Finset.range (n + 1), b k * ((k : ℝ) - n * μ) ^ 2 = n * μ * (1 - μ))
    (hgood : ∀ k : ℕ, ((k : ℝ) - n * μ) ^ 2 ≤ (n * δ) ^ 2 → |x k| ≤ A)
    (hbad : ∀ k : ℕ, |x k| ≤ Cb) :
    |∑ k ∈ Finset.range (n + 1), b k * x k| ≤ A + Cb / (n * δ) ^ 2 * (n * μ * (1 - μ)) := by
  have hterm : ∀ k, |b k * x k| ≤ b k * A + Cb / (n * δ) ^ 2 * (b k * ((k : ℝ) - n * μ) ^ 2) := by
    intro k
    rw [abs_mul, abs_of_nonneg (hb0 k)]
    have hc : 0 ≤ Cb / (n * δ) ^ 2 := by positivity
    by_cases hk : ((k : ℝ) - n * μ) ^ 2 ≤ (n * δ) ^ 2
    · have h1 : b k * |x k| ≤ b k * A := mul_le_mul_of_nonneg_left (hgood k hk) (hb0 k)
      have h2 : 0 ≤ Cb / (n * δ) ^ 2 * (b k * ((k : ℝ) - n * μ) ^ 2) :=
        mul_nonneg hc (mul_nonneg (hb0 k) (sq_nonneg _))
      linarith
    · push Not at hk
      have hr : 1 ≤ ((k : ℝ) - n * μ) ^ 2 / (n * δ) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have e : Cb / (n * δ) ^ 2 * (b k * ((k : ℝ) - n * μ) ^ 2) =
          (b k * Cb) * (((k : ℝ) - n * μ) ^ 2 / (n * δ) ^ 2) := by
        field_simp
      have h1 : b k * |x k| ≤ b k * Cb := mul_le_mul_of_nonneg_left (hbad k) (hb0 k)
      have h2 : b k * Cb * 1 ≤ b k * Cb * (((k : ℝ) - n * μ) ^ 2 / (n * δ) ^ 2) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg (hb0 k) hCb)
      have h3 : 0 ≤ b k * A := mul_nonneg (hb0 k) hA
      rw [e]; linarith
  calc |∑ k ∈ Finset.range (n + 1), b k * x k|
      ≤ ∑ k ∈ Finset.range (n + 1), |b k * x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (b k * A +
          Cb / (n * δ) ^ 2 * (b k * ((k : ℝ) - n * μ) ^ 2)) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = A + Cb / (n * δ) ^ 2 * (n * μ * (1 - μ)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hb1, hbv, one_mul]

lemma final_arith {ε A Cb m n μ δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hCb : 0 < Cb) (hμ0 : 0 < μ)
    (hμ1 : μ ≤ 1) (hA : A = ε / 2 + Cb * m) (hmn : m < ε / (4 * Cb))
    (hvar : Cb / (n * δ ^ 2) < ε / 4) : A + Cb / (n * δ) ^ 2 * (n * μ * (1 - μ)) < ε := by
  have h1 : Cb * m < ε / 4 := by
    rw [lt_div_iff₀ (by positivity)] at hmn; linarith
  have hμμ : μ * (1 - μ) ≤ 1 := by nlinarith
  have hμμ0 : 0 ≤ μ * (1 - μ) := mul_nonneg hμ0.le (by linarith)
  have e : Cb / (n * δ) ^ 2 * (n * μ * (1 - μ)) = Cb / (n * δ ^ 2) * (μ * (1 - μ)) := by
    field_simp
  have hc : 0 ≤ Cb / (n * δ ^ 2) := by positivity
  have h2 : Cb / (n * δ ^ 2) * (μ * (1 - μ)) ≤ Cb / (n * δ ^ 2) * 1 :=
    mul_le_mul_of_nonneg_left hμμ hc
  rw [e, hA]; linarith

/-- (3.14): `q_a^{(n)}(μ) → ω(d_a/μ)` for `μ ∈ (0, 1]`. -/
lemma q_tendsto {B : Type} [MeasurableSpace B] (M : Market B)
    (hd : 0 < M.d)
    (hF : ∀ n, IsProbabilityMeasure (M.F n) ∧ M.F n (Set.Iio 0) = 0)
    (h31 : Tendsto (fun n : ℕ => ∫⁻ D, ENNReal.ofReal ((D / n - M.d) ^ 2) ∂(M.F n)) atTop
      (𝓝 0))
    (hω : IsRegularAllocation M.ω)
    (hl : ∃ K : ℝ, ∀ d t, 0 ≤ d → 0 ≤ t → 0 ≤ M.l d t ∧ M.l d t ≤ K)
    (hldecay : ∀ ε > 0, ∃ K : ℝ, ∀ d t, K ≤ d → K ≤ t →
      |M.l d t| ≤ ε * (1 / Real.sqrt t + 1 / Real.sqrt d))
    (hΩeq : ∀ d t, 0 ≤ d → 0 ≤ t → M.Ω d t = M.ω (d / t) + M.l d t)
    (hΩmeas : ∀ t, Measurable (fun d => M.Ω d t))
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) :
    Tendsto (fun n => M.q n μ) atTop (𝓝 (M.ω (M.d / μ))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set w := M.d / μ with hwdef
  have hw : 0 < w := div_pos hd hμ0
  have hcω : ContinuousAt M.ω w := hω.2.1.continuousOn.continuousAt (Ioi_mem_nhds hw)
  obtain ⟨η, hη, hωη⟩ := Metric.continuousAt_iff.mp hcω (ε / 4) (by linarith)
  obtain ⟨K, hK⟩ := hl
  have hK0 : 0 ≤ K := le_trans (hK 0 0 le_rfl le_rfl).1 (hK 0 0 le_rfl le_rfl).2
  obtain ⟨K₁, hK₁⟩ := hldecay (ε / 8) (by linarith)
  set K₂ := max K₁ 1 with hK₂
  have hK₂1 : 1 ≤ K₂ := le_max_right _ _
  have hK₂K₁ : K₁ ≤ K₂ := le_max_left _ _
  set δ := min (min (μ / 2) (M.d / 2)) (η * μ ^ 2 / (4 * (μ + M.d))) with hδdef
  have hδ : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hδμ : δ ≤ μ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδd : δ ≤ M.d / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδη : δ ≤ η * μ ^ 2 / (4 * (μ + M.d)) := min_le_right _ _
  set Cb := 2 + K with hCb
  have hCb0 : 0 < Cb := by linarith
  set S : ℕ → Set ℝ := fun n => {D | δ < |D / n - M.d|} with hS
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt measurable_const (by fun_prop)
  set m : ℕ → ℝ := fun n => (M.F n).real (S n) with hmdef
  have hm : Tendsto m atTop (𝓝 0) := by
    have hδ2 : ENNReal.ofReal (δ ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hle : ∀ n, M.F n (S n) ≤
        (∫⁻ D, ENNReal.ofReal ((D / n - M.d) ^ 2) ∂(M.F n)) / ENNReal.ofReal (δ ^ 2) := by
      intro n
      refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div ?_ hδ2 ENNReal.ofReal_ne_top)
      · intro D hD
        simp only [S, Set.mem_ofPred_eq] at hD ⊢
        apply ENNReal.ofReal_le_ofReal
        rw [← sq_abs (D / n - M.d)]
        exact pow_le_pow_left₀ hδ.le hD.le 2
      · exact (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
    have hE : Tendsto (fun n => M.F n (S n)) atTop (𝓝 0) := by
      have h2 := ENNReal.Tendsto.div_const h31 (Or.inr hδ2)
      rw [ENNReal.zero_div] at h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
        (fun n => bot_le) hle
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    simp only [ENNReal.toReal_zero] at this
    exact this
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hm (ε / (4 * Cb)) (by positivity)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (4 * Cb / (ε * δ ^ 2))
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (2 * K₂ / μ + 2 * K₂ / M.d + 1)
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : (N₂ : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : (N₃ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hA1 : 0 ≤ 2 * K₂ / μ := by positivity
  have hA2 : 0 ≤ 2 * K₂ / M.d := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hnμ : K₂ ≤ n * μ / 2 := by
    have : 2 * K₂ / μ < n := by linarith
    rw [div_lt_iff₀ hμ0] at this
    linarith
  have hnd : K₂ ≤ n * M.d / 2 := by
    have : 2 * K₂ / M.d < n := by linarith
    rw [div_lt_iff₀ hd] at this
    linarith
  have hmn : m n < ε / (4 * Cb) := by
    have := hN₁ n hn1
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hm0 : 0 ≤ m n := measureReal_nonneg
  have hvar : Cb / (n * δ ^ 2) < ε / 4 := arith_var hCb0 hε hδ hnpos (by linarith)
  haveI := (hF n).1
  have hDae : ∀ᵐ D ∂(M.F n), 0 ≤ D := ae_nonneg_of_Iio _ (hF n).2
  have hΩb : ∀ D, 0 ≤ D → ∀ k : ℕ, 0 ≤ M.Ω D k ∧ M.Ω D k ≤ 1 + K := by
    intro D hD k
    rw [hΩeq D k hD (Nat.cast_nonneg k)]
    have h1 := hω.1 (D / k) (div_nonneg hD (Nat.cast_nonneg k))
    have h2 := hK D k hD (Nat.cast_nonneg k)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hωw := hω.1 w hw.le
  have hptbad : ∀ D, 0 ≤ D → ∀ k : ℕ, |M.Ω D k - M.ω w| ≤ Cb := by
    intro D hD k
    have := hΩb D hD k
    rw [abs_le]; constructor <;> linarith [this.1, this.2, hωw.1, hωw.2]
  have hintΩ : ∀ k : ℕ, Integrable (fun D => M.Ω D k) (M.F n) := by
    intro k
    refine (integrable_const (1 + K)).mono' (hΩmeas k).aestronglyMeasurable ?_
    filter_upwards [hDae] with D hD
    have := hΩb D hD k
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have hintabs : ∀ k : ℕ, Integrable (fun D => |M.Ω D k - M.ω w|) (M.F n) :=
    fun k => ((hintΩ k).sub (integrable_const _)).abs
  have hbad : ∀ k : ℕ, ∫ D, |M.Ω D k - M.ω w| ∂(M.F n) ≤ Cb := by
    intro k
    have : ∫ D, |M.Ω D k - M.ω w| ∂(M.F n) ≤ ∫ _D, Cb ∂(M.F n) :=
      integral_mono_ae (hintabs k) (integrable_const _)
        (hDae.mono fun D hD => hptbad D hD k)
    simpa using this
  have hgood : ∀ k : ℕ, ((k : ℝ) - n * μ) ^ 2 ≤ (n * δ) ^ 2 →
      ∫ D, |M.Ω D k - M.ω w| ∂(M.F n) ≤ ε / 2 + Cb * m n := by
    intro k hk
    have hk' : |(k : ℝ) - n * μ| ≤ n * δ := by
      have := sq_le_sq.mp hk
      rwa [abs_of_pos (by positivity : (0 : ℝ) < n * δ)] at this
    have hkge : n * μ / 2 ≤ k := by
      have := (abs_le.mp hk').1
      have : n * δ ≤ n * (μ / 2) := mul_le_mul_of_nonneg_left hδμ hnpos.le
      linarith
    have hkpos : (0 : ℝ) < k := by linarith
    have hpt : ∀ D, 0 ≤ D → |M.Ω D k - M.ω w| ≤ ε / 2 + Cb * (S n).indicator (fun _ => (1 : ℝ)) D := by
      intro D hD
      by_cases hDS : D ∈ S n
      · rw [Set.indicator_of_mem hDS, mul_one]
        linarith [hptbad D hD k]
      · rw [Set.indicator_of_notMem hDS, mul_zero, add_zero]
        simp only [S, Set.mem_ofPred_eq, not_lt] at hDS
        have hDn : |D - n * M.d| ≤ n * δ := by
          have : D - n * M.d = n * (D / n - M.d) := by field_simp
          rw [this, abs_mul, abs_of_pos hnpos]
          exact mul_le_mul_of_nonneg_left hDS hnpos.le
        have hDge : n * M.d / 2 ≤ D := by
          have := (abs_le.mp hDn).1
          have : n * δ ≤ n * (M.d / 2) := mul_le_mul_of_nonneg_left hδd hnpos.le
          linarith
        -- the `l` term
        have hl1 : |M.l D k| ≤ ε / 4 := by
          have h := hK₁ D k (by linarith) (by linarith)
          have hsk : 1 / Real.sqrt k ≤ 1 := by
            rw [div_le_one (Real.sqrt_pos.mpr hkpos)]
            exact Real.one_le_sqrt.mpr (by linarith)
          have hsD : 1 / Real.sqrt D ≤ 1 := by
            rw [div_le_one (Real.sqrt_pos.mpr (by linarith))]
            exact Real.one_le_sqrt.mpr (by linarith)
          calc |M.l D k| ≤ ε / 8 * (1 / Real.sqrt k + 1 / Real.sqrt D) := h
            _ ≤ ε / 8 * (1 + 1) := by gcongr
            _ = ε / 4 := by ring
        -- the `ω` term
        have hdist : |D / k - w| < η :=
          arith_dist hkpos hμ0 hd hη hnpos hDn hk' hkge hδη
        have hω1 : |M.ω (D / k) - M.ω w| < ε / 4 := by
          have := hωη (by rw [Real.dist_eq]; exact hdist)
          rwa [Real.dist_eq] at this
        rw [hΩeq D k hD (Nat.cast_nonneg k)]
        calc |M.ω (D / k) + M.l D k - M.ω w|
            = |(M.ω (D / k) - M.ω w) + M.l D k| := by ring_nf
          _ ≤ |M.ω (D / k) - M.ω w| + |M.l D k| := abs_add_le _ _
          _ ≤ ε / 2 := by linarith
    have hint2 : Integrable (fun D => ε / 2 + Cb * (S n).indicator (fun _ => (1 : ℝ)) D) (M.F n) :=
      (integrable_const _).add (((integrable_const (1 : ℝ)).indicator (hSmeas n)).const_mul Cb)
    calc ∫ D, |M.Ω D k - M.ω w| ∂(M.F n)
        ≤ ∫ D, (ε / 2 + Cb * (S n).indicator (fun _ => (1 : ℝ)) D) ∂(M.F n) :=
          integral_mono_ae (hintabs k) hint2 (hDae.mono fun D hD => hpt D hD)
      _ = ε / 2 + Cb * m n := by
          rw [integral_add (integrable_const _)
            (((integrable_const (1 : ℝ)).indicator (hSmeas n)).const_mul Cb),
            integral_const, integral_const_mul, integral_indicator_const _ (hSmeas n)]
          simp [m]
  -- assemble
  have habs : ∀ k : ℕ, |(∫ D, M.Ω D k ∂(M.F n)) - M.ω w| ≤ ∫ D, |M.Ω D k - M.ω w| ∂(M.F n) := by
    intro k
    have : (∫ D, M.Ω D k ∂(M.F n)) - M.ω w = ∫ D, (M.Ω D k - M.ω w) ∂(M.F n) := by
      rw [integral_sub (hintΩ k) (integrable_const _), integral_const]
      simp
    rw [this]
    exact abs_integral_le_integral_abs
  set b : ℕ → ℝ := fun k => (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    have : 0 ≤ 1 - μ := by linarith
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hμ0.le _)) (pow_nonneg this _)
  have hq : M.q n μ - M.ω w =
      ∑ k ∈ Finset.range (n + 1), b k * ((∫ D, M.Ω D k ∂(M.F n)) - M.ω w) := by
    have hb1 : ∑ k ∈ Finset.range (n + 1), b k = 1 := bern_sum_one n μ
    calc M.q n μ - M.ω w = M.q n μ - M.ω w * ∑ k ∈ Finset.range (n + 1), b k := by
          rw [hb1, mul_one]
      _ = _ := by
          unfold Market.q
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [b]; ring
  rw [Real.dist_eq, hq]
  have hb1 : ∑ k ∈ Finset.range (n + 1), b k = 1 := bern_sum_one n μ
  have hbv : ∑ k ∈ Finset.range (n + 1), b k * ((k : ℝ) - n * μ) ^ 2 = n * μ * (1 - μ) :=
    bern_var n μ
  have hA0 : 0 ≤ ε / 2 + Cb * m n := by positivity
  refine lt_of_le_of_lt (sum_bound n μ δ (ε / 2 + Cb * m n) Cb hnpos hδ hA0 hCb0.le b _ hb0 hb1
    hbv (fun k hk => le_trans (habs k) (hgood k hk)) (fun k => le_trans (habs k) (hbad k))) ?_
  exact final_arith hnpos hδ hCb0 hμ0 hμ1 rfl hmn hvar

section FInt
variable {B : Type} [MeasurableSpace B] (β : Measure B) [IsProbabilityMeasure β]
  (f : B → ℝ → ℝ) (hf01 : ∀ b x, 0 ≤ x → f b x ∈ Set.Icc (0 : ℝ) 1)
  (hfmeas : Measurable (Function.uncurry f))

include hfmeas in
lemma fmeas (x : ℝ) : Measurable (fun b => f b x) :=
  hfmeas.comp (measurable_id.prodMk measurable_const)

include hf01 hfmeas in
lemma fint {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun b => f b x) β ∧ ∫ b, f b x ∂β ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (fun b => f b x) β := by
    refine (integrable_const (1 : ℝ)).mono' (fmeas f hfmeas x).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b x hx
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  refine ⟨hint, integral_nonneg fun b => (hf01 b x hx).1, ?_⟩
  have : ∫ b, f b x ∂β ≤ ∫ _b, (1 : ℝ) ∂β :=
    integral_mono hint (integrable_const _) fun b => (hf01 b x hx).2
  simpa using this

include hf01 hfmeas in
lemma fint_mono (hfmono : ∀ b, MonotoneOn (f b) (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : ∫ b, f b x ∂β ≤ ∫ b, f b y ∂β :=
  integral_mono (fint β f hf01 hfmeas hx).1 (fint β f hf01 hfmeas (le_trans hx hxy)).1
    fun b => hfmono b (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_trans hx hxy)) hxy

include hf01 hfmeas in
lemma fint_continuousOn (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) (c : ℝ → ℝ) (s : Set ℝ)
    (hc : ContinuousOn c s) (hc0 : ∀ μ ∈ s, 0 ≤ c μ) :
    ContinuousOn (fun μ => ∫ b, f b (c μ) ∂β) s := by
  apply continuousOn_of_dominated (bound := fun _ => 1)
  · intro μ _
    exact (fmeas f hfmeas (c μ)).aestronglyMeasurable
  · intro μ hμ
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b _ (hc0 μ hμ)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun b => ?_
    exact (hfcont b).comp hc (fun μ hμ => Set.mem_Ici.mpr (hc0 μ hμ))

include hf01 hfmeas in
lemma fint_tendsto (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) {ι : Type} {l : Filter ι}
    [l.IsCountablyGenerated] (u : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) (hu : Tendsto u l (𝓝 x))
    (hu0 : ∀ᶠ i in l, 0 ≤ u i) :
    Tendsto (fun i => ∫ b, f b (u i) ∂β) l (𝓝 (∫ b, f b x ∂β)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 1)
  · exact Filter.Eventually.of_forall fun i => (fmeas f hfmeas (u i)).aestronglyMeasurable
  · filter_upwards [hu0] with i hi
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b _ hi
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun b => ?_
    have h1 : Tendsto u l (𝓝[Set.Ici 0] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu, hu0⟩
    exact ((hfcont b) x (Set.mem_Ici.mpr hx)).tendsto.comp h1

end FInt

lemma omega_facts (ω : ℝ → ℝ) (hω : IsRegularAllocation ω) {d : ℝ} (hd : 0 < d) :
    ∃ L, sSup (ω '' Set.Ici 0) = L ∧ Tendsto (fun μ => ω (d / μ)) (𝓝[>] 0) (𝓝 L) ∧ 0 ≤ L := by
  obtain ⟨L, -, hL⟩ := hω.2.2.2.2.2.1
  have hmono := hω.2.2.2.1
  have hle : ∀ x, 0 ≤ x → ω x ≤ L := by
    intro x hx
    exact ge_of_tendsto hL ((eventually_ge_atTop x).mono fun y hy =>
      hmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_trans hx hy)) hy)
  refine ⟨L, ?_, ?_, ?_⟩
  · apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.Nonempty.image _ ⟨0, le_refl _⟩)
    · rintro _ ⟨x, hx, rfl⟩; exact hle x hx
    · intro w hw
      obtain ⟨y, hy1, hy2⟩ := ((hL.eventually (lt_mem_nhds hw)).and (eventually_ge_atTop 0)).exists
      exact ⟨ω y, ⟨y, hy2, rfl⟩, hy1⟩
  · have h : Tendsto (fun μ : ℝ => d / μ) (𝓝[>] 0) atTop := by
      simp only [div_eq_mul_inv]
      exact tendsto_inv_nhdsGT_zero.const_mul_atTop hd
    exact hL.comp h
  · exact le_trans (hω.1 0 le_rfl).1 (hle 0 le_rfl)

end EqExpL2Aux

open EqExpL2Aux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing) :
    (∀ p : ℝ, 0 < p → 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β →
      (∃! μ : ℝ, μ ∈ Set.Ioc (0 : ℝ) 1 ∧ μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β) ∧
      Tendsto (fun n : ℕ => M.muN n (Measure.dirac p)) atTop (𝓝 (M.muLim p))) ∧
    (∀ μ : ℝ, μ ∈ Set.Ioc (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => M.q n μ) atTop (𝓝 (M.ω (M.d / μ)))) := by
  obtain ⟨hd, hF, -, h31, -, hβ, hω, -, hΩt, hl, hldecay, hΩeq, hΩmeas, hf01, hfmono, hfderiv,
    -, hfmeas, -, -, -, -⟩ := hM
  haveI := hβ
  have hqlim : ∀ μ : ℝ, μ ∈ Set.Ioc (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => M.q n μ) atTop (𝓝 (M.ω (M.d / μ))) := fun μ hμ =>
    q_tendsto M hd hF h31 hω hl hldecay hΩeq hΩmeas hμ.1 hμ.2
  refine ⟨?_, hqlim⟩
  intro p hp hpos
  have hfcont : ∀ b, ContinuousOn (M.f b) (Set.Ici 0) := by
    intro b x hx
    exact (hfderiv b x hx).1.continuousWithinAt
  obtain ⟨K, hK⟩ := hl
  -- facts about `q_n` (Bernstein polynomial with non-increasing, non-negative coefficients)
  have hqfacts : ∀ n : ℕ, (∀ μ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.q n μ) ∧
      AntitoneOn (M.q n) (Set.Icc 0 1) ∧ Continuous (M.q n) := by
    intro n
    haveI := (hF n).1
    set a : ℕ → ℝ := fun k => ∫ D, M.Ω D k ∂(M.F n) with ha
    have hqa : ∀ μ, M.q n μ = bern n a μ := fun μ => rfl
    have hDae : ∀ᵐ D ∂(M.F n), 0 ≤ D := ae_nonneg_of_Iio _ (hF n).2
    have hΩb : ∀ D, 0 ≤ D → ∀ k : ℕ, 0 ≤ M.Ω D k ∧ M.Ω D k ≤ 1 + K := by
      intro D hD k
      rw [hΩeq D k hD (Nat.cast_nonneg k)]
      have h1 := hω.1 (D / k) (div_nonneg hD (Nat.cast_nonneg k))
      have h2 := hK D k hD (Nat.cast_nonneg k)
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hintk : ∀ k : ℕ, Integrable (fun D => M.Ω D k) (M.F n) := by
      intro k
      refine (integrable_const (1 + K)).mono' (hΩmeas k).aestronglyMeasurable ?_
      filter_upwards [hDae] with D hD
      have := hΩb D hD k
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
    have ha0 : ∀ k, 0 ≤ a k := fun k =>
      integral_nonneg_of_ae (hDae.mono fun D hD => (hΩb D hD k).1)
    have hanti : Antitone a := by
      apply antitone_nat_of_succ_le
      intro k
      apply integral_mono_ae (hintk (k + 1)) (hintk k)
      filter_upwards [hDae] with D hD
      have h := hΩt D (k : ℝ) ((k : ℝ) + 1) hD (Nat.cast_nonneg k) (by linarith)
      rw [Nat.cast_succ]; exact h
    refine ⟨fun μ hμ => ?_, fun x hx y hy hxy => ?_, ?_⟩
    · rw [hqa]; exact bern_nonneg n ha0 hμ
    · rw [hqa, hqa]; exact bern_antitone n a hanti hx hy hxy
    · have : M.q n = bern n a := funext hqa
      rw [this]; exact bern_continuous n a
  -- `ψ_n` for the point mass at `p`
  set ψ : ℕ → ℝ → ℝ := fun n μ => ∫ b, M.f b (p * M.q n μ) ∂M.β with hψdef
  have hpsi : ∀ n μ, M.psi n (Measure.dirac p) μ = ψ n μ := by
    intro n μ
    simp only [Market.psi, ψ]
    congr 1
    funext b
    rw [integral_dirac]
  have hψ01 : ∀ n, ∀ μ ∈ Set.Icc (0 : ℝ) 1, ψ n μ ∈ Set.Icc (0 : ℝ) 1 := fun n μ hμ =>
    (fint M.β M.f hf01 hfmeas (mul_nonneg hp.le ((hqfacts n).1 μ hμ))).2
  have hψanti : ∀ n, AntitoneOn (ψ n) (Set.Icc 0 1) := by
    intro n x hx y hy hxy
    exact fint_mono M.β M.f hf01 hfmeas hfmono (mul_nonneg hp.le ((hqfacts n).1 y hy))
      (mul_le_mul_of_nonneg_left ((hqfacts n).2.1 hx hy hxy) hp.le)
  have hψcont : ∀ n, ContinuousOn (ψ n) (Set.Icc 0 1) := fun n =>
    fint_continuousOn M.β M.f hf01 hfmeas hfcont (fun μ => p * M.q n μ) _
      (continuousOn_const.mul (hqfacts n).2.2.continuousOn)
      (fun μ hμ => mul_nonneg hp.le ((hqfacts n).1 μ hμ))
  -- the equilibrium `μ_n(p)`
  have hmuN : ∀ n, M.muN n (Measure.dirac p) ∈ Set.Icc (0 : ℝ) 1 ∧
      ψ n (M.muN n (Measure.dirac p)) = M.muN n (Measure.dirac p) := by
    intro n
    have hex : ∃ μ ∈ Set.Icc (0 : ℝ) 1, M.psi n (Measure.dirac p) μ = μ := by
      have hivt := intermediate_value_Icc' (zero_le_one' ℝ)
        ((hψcont n).sub (continuousOn_id (s := Set.Icc (0 : ℝ) 1)))
      have h0 : (0 : ℝ) ∈ Set.Icc (ψ n 1 - id 1) (ψ n 0 - id 0) := by
        have e1 := hψ01 n 1 ⟨zero_le_one, le_refl _⟩
        have e0 := hψ01 n 0 ⟨le_refl _, zero_le_one⟩
        simp only [id]
        constructor <;> linarith [e1.2, e0.1]
      obtain ⟨μ, hμ, hμeq⟩ := hivt h0
      refine ⟨μ, hμ, ?_⟩
      simp only [Pi.sub_apply, id] at hμeq
      rw [hpsi]; linarith
    unfold Market.muN
    rw [dif_pos hex]
    have := hex.choose_spec
    rw [hpsi] at this
    exact this
  -- the mean-field map `Ψ(μ) = 𝔼 f_B(p ω(d/μ))`
  set Ψ : ℝ → ℝ := fun μ => ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β with hΨdef
  have hωd0 : ∀ μ, 0 < μ → 0 ≤ M.ω (M.d / μ) := fun μ hμ =>
    (hω.1 _ (div_nonneg hd.le hμ.le)).1
  have hΨ01 : ∀ μ, 0 < μ → Ψ μ ∈ Set.Icc (0 : ℝ) 1 := fun μ hμ =>
    (fint M.β M.f hf01 hfmeas (mul_nonneg hp.le (hωd0 μ hμ))).2
  have hΨanti : AntitoneOn Ψ (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    apply fint_mono M.β M.f hf01 hfmeas hfmono (mul_nonneg hp.le (hωd0 y hy'))
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact hω.2.2.2.1 (Set.mem_Ici.mpr (div_nonneg hd.le hy'.le))
      (Set.mem_Ici.mpr (div_nonneg hd.le hx'.le)) (div_le_div_of_nonneg_left hd.le hx' hxy)
  have hΨcont : ContinuousOn Ψ (Set.Ioi 0) := by
    apply fint_continuousOn M.β M.f hf01 hfmeas hfcont (fun μ => p * M.ω (M.d / μ)) _ _
      (fun μ hμ => mul_nonneg hp.le (hωd0 μ hμ))
    apply continuousOn_const.mul
    refine hω.2.1.continuousOn.comp (continuousOn_const.div continuousOn_id
      (fun x hx => ne_of_gt hx)) ?_
    intro x hx
    exact div_pos hd hx
  -- the limit of `Ψ` at `0+`
  obtain ⟨L, hLsup, hLlim, hL0⟩ := omega_facts M.ω hω hd
  have hΨ0 : Tendsto Ψ (𝓝[>] 0) (𝓝 (∫ b, M.f b (p * M.omegaSup) ∂M.β)) := by
    rw [Market.omegaSup, hLsup]
    apply fint_tendsto M.β M.f hf01 hfmeas hfcont (fun μ => p * M.ω (M.d / μ))
      (mul_nonneg hp.le hL0) (hLlim.const_mul p)
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    exact mul_nonneg hp.le (hωd0 μ hμ)
  -- existence and uniqueness of `μ_a(p)`
  have hexL : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = Ψ μ := by
    set c0 := ∫ b, M.f b (p * M.omegaSup) ∂M.β
    have h1 : ∀ᶠ μ in 𝓝[>] (0 : ℝ), c0 / 2 < Ψ μ :=
      hΨ0.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ μ in 𝓝[>] (0 : ℝ), μ < min (c0 / 2) 1 :=
      (nhdsWithin_le_nhds) (gt_mem_nhds (lt_min (by linarith) one_pos))
    have h3 : ∀ᶠ μ in 𝓝[>] (0 : ℝ), 0 < μ := self_mem_nhdsWithin
    obtain ⟨μ₀, hμ₀1, hμ₀2, hμ₀3⟩ := (h1.and (h2.and h3)).exists
    have hμ₀le : μ₀ ≤ 1 := le_trans (le_of_lt (lt_of_lt_of_le hμ₀2 (min_le_right _ _))) le_rfl
    have hsub : Set.Icc μ₀ 1 ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hμ₀3 hx.1
    have hivt := intermediate_value_Icc hμ₀le
      ((continuousOn_id (s := Set.Icc μ₀ 1)).sub (hΨcont.mono hsub))
    have h0 : (0 : ℝ) ∈ Set.Icc (id μ₀ - Ψ μ₀) (id 1 - Ψ 1) := by
      have e1 := hΨ01 1 one_pos
      have e2 : μ₀ < c0 / 2 := lt_of_lt_of_le hμ₀2 (min_le_left _ _)
      simp only [id]
      constructor <;> linarith [e1.2]
    obtain ⟨μ, hμ, hμeq⟩ := hivt h0
    simp only [Pi.sub_apply, id] at hμeq
    exact ⟨μ, ⟨lt_of_lt_of_le hμ₀3 hμ.1, hμ.2⟩, by linarith⟩
  have huniq : ∀ μ₁ ∈ Set.Ioc (0 : ℝ) 1, ∀ μ₂ ∈ Set.Ioc (0 : ℝ) 1,
      μ₁ = Ψ μ₁ → μ₂ = Ψ μ₂ → μ₁ ≤ μ₂ := by
    intro μ₁ h₁ μ₂ h₂ e₁ e₂
    by_contra hlt
    push Not at hlt
    have := hΨanti (show (0 : ℝ) < μ₂ from h₂.1) (show (0 : ℝ) < μ₁ from h₁.1) hlt.le
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨μ, hμ, hμeq⟩ := hexL
    refine ⟨μ, ⟨hμ, hμeq⟩, ?_⟩
    rintro μ' ⟨hμ', hμ'eq⟩
    exact le_antisymm (huniq μ' hμ' μ hμ hμ'eq hμeq) (huniq μ hμ μ' hμ' hμeq hμ'eq)
  -- convergence `μ_n(p) → μ_a(p)`
  have hmuL : M.muLim p ∈ Set.Ioc (0 : ℝ) 1 ∧ M.muLim p = Ψ (M.muLim p) := by
    unfold Market.muLim
    rw [dif_pos hexL]
    exact hexL.choose_spec
  set μs := M.muLim p with hμs
  have hψlim : ∀ μ ∈ Set.Ioc (0 : ℝ) 1, Tendsto (fun n => ψ n μ) atTop (𝓝 (Ψ μ)) := by
    intro μ hμ
    apply fint_tendsto M.β M.f hf01 hfmeas hfcont (fun n => p * M.q n μ)
      (mul_nonneg hp.le (hωd0 μ hμ.1)) ((hqlim μ hμ).const_mul p)
    exact Filter.Eventually.of_forall fun n =>
      mul_nonneg hp.le ((hqfacts n).1 μ ⟨hμ.1.le, hμ.2⟩)
  rw [tendsto_order]
  constructor
  · intro a ha
    set s := max a (μs / 2) with hs
    have hs0 : 0 < s := lt_of_lt_of_le (by linarith [hmuL.1.1]) (le_max_right _ _)
    have hsμ : s < μs := max_lt ha (by linarith [hmuL.1.1])
    have hs1 : s ≤ 1 := le_trans hsμ.le hmuL.1.2
    have hΨs : s < Ψ s := by
      have := hΨanti (show (0 : ℝ) < s from hs0) (show (0 : ℝ) < μs from hmuL.1.1) hsμ.le
      linarith [hmuL.2]
    have hev := (hψlim s ⟨hs0, hs1⟩).eventually (lt_mem_nhds hΨs)
    filter_upwards [hev] with n hn
    refine lt_of_le_of_lt (le_max_left a (μs / 2)) ?_
    by_contra hcon
    push Not at hcon
    have h1 := hψanti n (hmuN n).1 ⟨hs0.le, hs1⟩ hcon
    rw [(hmuN n).2] at h1
    linarith
  · intro b hb
    by_cases hμ1 : μs = 1
    · exact Filter.Eventually.of_forall fun n => lt_of_le_of_lt (hmuN n).1.2 (by linarith)
    · have hμlt : μs < 1 := lt_of_le_of_ne hmuL.1.2 hμ1
      set t := min b 1 with ht
      have htμ : μs < t := lt_min hb hμlt
      have ht0 : 0 < t := lt_trans hmuL.1.1 htμ
      have ht1 : t ≤ 1 := min_le_right _ _
      have hΨt : Ψ t < t := by
        have := hΨanti (show (0 : ℝ) < μs from hmuL.1.1) (show (0 : ℝ) < t from ht0) htμ.le
        linarith [hmuL.2]
      have hev := (hψlim t ⟨ht0, ht1⟩).eventually (gt_mem_nhds hΨt)
      filter_upwards [hev] with n hn
      refine lt_of_lt_of_le ?_ (min_le_left b 1)
      by_contra hcon
      push Not at hcon
      have h1 := hψanti n ⟨ht0.le, ht1⟩ (hmuN n).1 hcon
      rw [(hmuN n).2] at h1
      linarith
