-- Prove2me | solution 1 for ContagionGrowth.FluidLimit.eq_27_28
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:28:45.698753+00:00
-- url     : https://prove2.me/submissions/d6d72e1d-d6bd-42fe-9386-b179109b112a

import Mathlib

namespace CGAux2

open MeasureTheory ProbabilityTheory Filter Topology Real

lemma key_int {r : ℝ} (hr : 0 < r) (p : ℕ) :
    ∫ x in Set.Ioi 0, r * Real.exp (-(r * x)) * x ^ p = (p.factorial : ℝ) / r ^ p := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (p : ℝ) + 1) (by positivity) hr
  have e : ∀ x ∈ Set.Ioi (0:ℝ), r * Real.exp (-(r * x)) * x ^ p =
      r * (x ^ ((p : ℝ) + 1 - 1) * Real.exp (-(r * x))) := by
    intro x _; rw [add_sub_cancel_right, Real.rpow_natCast]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h,
    Real.Gamma_nat_eq_factorial]
  have : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast, one_div, inv_pow, pow_succ]
  field_simp

lemma key_integrableOn {r : ℝ} (hr : 0 < r) (p : ℕ) :
    IntegrableOn (fun x => r * Real.exp (-(r * x)) * x ^ p) (Set.Ioi 0) := by
  by_contra h
  have h0 := integral_undef h
  rw [key_int hr p] at h0
  have : (0 : ℝ) < (p.factorial : ℝ) / r ^ p := by have := p.factorial_pos; positivity
  linarith

lemma dens {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (gammaPDF 1 r x).toReal = Set.indicator (Set.Ici 0) (fun x => r * Real.exp (-(r * x))) x := by
  by_cases h : 0 ≤ x
  · have h' : x ∈ Set.Ici (0:ℝ) := h
    rw [Set.indicator_of_mem h', gammaPDF, gammaPDFReal, if_pos h]
    simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
    exact ENNReal.toReal_ofReal (by positivity)
  · have h' : x ∉ Set.Ici (0:ℝ) := h
    rw [Set.indicator_of_notMem h', gammaPDF, gammaPDFReal, if_neg h]
    simp

lemma meas_pdf (r : ℝ) : Measurable (gammaPDF 1 r) :=
  (measurable_gammaPDFReal 1 r).ennreal_ofReal

lemma ae_lt (r : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF 1 r x < ⊤ :=
  ae_of_all _ fun _ => ENNReal.ofReal_lt_top

lemma integral_pow_exp {r : ℝ} (hr : 0 < r) (p : ℕ) :
    ∫ x, x ^ p ∂(expMeasure r) = (p.factorial : ℝ) / r ^ p := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul (meas_pdf r) (ae_lt r)]
  have : (fun x => (gammaPDF 1 r x).toReal • x ^ p) =
      Set.indicator (Set.Ici 0) (fun x => r * Real.exp (-(r * x)) * x ^ p) := by
    funext x; rw [dens hr]
    by_cases h : x ∈ Set.Ici (0:ℝ) <;> simp [Set.indicator, h]
  rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, key_int hr]

lemma integrable_pow_exp {r : ℝ} (hr : 0 < r) (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (expMeasure r) := by
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff (meas_pdf r) (ae_lt r)]
  have : (fun x => x ^ p * (gammaPDF 1 r x).toReal) =
      Set.indicator (Set.Ici 0) (fun x => r * Real.exp (-(r * x)) * x ^ p) := by
    funext x; rw [dens hr]
    by_cases h : x ∈ Set.Ici (0:ℝ) <;> simp [Set.indicator, h, mul_comm]
  rw [this, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  exact key_integrableOn hr p

lemma memLp_id_exp {r : ℝ} (hr : 0 < r) : MemLp (id : ℝ → ℝ) 2 (expMeasure r) := by
  rw [memLp_two_iff_integrable_sq aestronglyMeasurable_id]
  simpa using integrable_pow_exp hr 2

lemma mean_exp {r : ℝ} (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = 1 / r := by
  have := integral_pow_exp hr 1
  simpa using this

lemma var_exp {r : ℝ} (hr : 0 < r) : Var[id; expMeasure r] = 1 / r ^ 2 := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [variance_eq_sub (memLp_id_exp hr)]
  have h2 : (expMeasure r)[id ^ 2] = 2 / r ^ 2 := by
    have := integral_pow_exp hr 2
    simpa using this
  have h1 : (expMeasure r)[id] = 1 / r := by simpa using mean_exp hr
  rw [h2, h1]; field_simp; ring

/-- Chebyshev for the sum of `k` i.i.d. `Exp(r)` variables. -/
lemma cheb {r : ℝ} (hr : 0 < r) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : Fin k => expMeasure r) {Δ | c ≤ |∑ i, Δ i - k / r|} ≤
      ENNReal.ofReal ((k / r ^ 2) / c ^ 2) := by
  haveI := isProbabilityMeasure_expMeasure hr
  set ν := Measure.pi fun _ : Fin k => expMeasure r
  have mp : ∀ i : Fin k, MeasurePreserving (Function.eval i) ν (expMeasure r) :=
    fun i => measurePreserving_eval (fun _ : Fin k => expMeasure r) i
  set X : Fin k → (Fin k → ℝ) → ℝ := fun i Δ => Δ i
  have hX : ∀ i, MemLp (X i) 2 ν := fun i => (memLp_id_exp hr).comp_measurePreserving (mp i)
  have hmean : ∀ i, ∫ Δ, X i Δ ∂ν = 1 / r := by
    intro i
    calc ∫ Δ, X i Δ ∂ν = ∫ x, x ∂(ν.map (Function.eval i)) := by
          rw [integral_map (f := fun x : ℝ => x) (mp i).aemeasurable aestronglyMeasurable_id]
      _ = 1 / r := by rw [(mp i).map_eq]; exact mean_exp hr
  have hvar : ∀ i, Var[X i; ν] = 1 / r ^ 2 := by
    intro i
    rw [← variance_id_map (measurable_pi_apply i).aemeasurable]
    have : ν.map (fun Δ => Δ i) = expMeasure r := (mp i).map_eq
    rw [this, var_exp hr]
  have hind : iIndepFun X ν := by
    have := iIndepFun_pi (μ := fun _ : Fin k => expMeasure r) (X := fun _ => (id : ℝ → ℝ))
      (fun _ => aemeasurable_id)
    exact this
  set S : (Fin k → ℝ) → ℝ := ∑ i, X i
  have hSapp : ∀ Δ, S Δ = ∑ i, Δ i := fun Δ => by simp [S, X, Finset.sum_apply]
  have hSm : MemLp S 2 ν := memLp_finsetSum' _ (fun i _ => hX i)
  have hES : ν[S] = k / r := by
    have : ν[S] = ∫ Δ, ∑ i, X i Δ ∂ν := by
      congr 1; funext Δ; exact Finset.sum_apply _ _ _
    rw [this, integral_finsetSum _ (fun i _ => (hX i).integrable one_le_two)]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hVS : Var[S; ν] = k / r ^ 2 := by
    simp only [S]
    rw [IndepFun.variance_sum (fun i _ => hX i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have := meas_ge_le_variance_div_sq hSm hc
  rw [hES, hVS] at this
  have hset : {Δ : Fin k → ℝ | c ≤ |∑ i, Δ i - k / r|} = {ω | c ≤ |S ω - k / r|} := by
    ext Δ; simp [hSapp]
  rw [hset]; exact this

end CGAux2

open CGAux2 MeasureTheory Filter Topology in
theorem solution (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (lbarN : ℕ → ℝ) (lb : ℝ) (hlb : 0 < lb)
    (hlbN : Tendsto lbarN atTop (𝓝 lb)) (k : ℕ → ℕ)
    (hk : Tendsto (fun n : ℕ => ((k n : ℝ) - γ * lbarN n * n) / n) atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n : ℕ =>
      (Measure.pi fun _ : Fin (k n) => ProbabilityTheory.expMeasure (n : ℝ))
        {Δ : Fin (k n) → ℝ | ε < |∑ i, Δ i - γ * lb|}) atTop (𝓝 0) := by
  intro ε hε
  have hkn : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 (γ * lb)) := by
    have h2 := hk.add (hlbN.const_mul γ)
    rw [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp; ring
  have hk2 : Tendsto (fun n : ℕ => ((k n : ℝ) / (n : ℝ) ^ 2) / (ε / 2) ^ 2) atTop
      (𝓝 0) := by
    have h3 := (hkn.mul tendsto_one_div_atTop_nhds_zero_nat).div_const ((ε / 2) ^ 2)
    rw [mul_zero, zero_div] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hup : Tendsto (fun n : ℕ => ENNReal.ofReal (((k n : ℝ) / (n : ℝ) ^ 2) / (ε / 2) ^ 2))
      atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hk2
    rwa [ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => bot_le) ?_
  have hclose : ∀ᶠ n : ℕ in atTop, |(k n : ℝ) / n - γ * lb| < ε / 2 := by
    have := (Metric.tendsto_nhds.mp hkn) (ε / 2) (by positivity)
    simpa [Real.dist_eq] using this
  filter_upwards [hclose, eventually_ne_atTop 0] with n hn hn0
  have hr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  refine le_trans (measure_mono ?_) (cheb hr (k n) (by positivity : (0:ℝ) < ε / 2))
  intro Δ hΔ
  simp only [Set.mem_setOf_eq] at hΔ ⊢
  have tri := abs_sub_le (∑ i, Δ i) ((k n : ℝ) / n) (γ * lb)
  linarith
