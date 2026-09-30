-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.bernoulli_tail
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:16:30.669611+00:00
-- url     : https://prove2.me/submissions/96354710-156d-4c06-9bb6-a7c43b0eaa40

import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
universe u

theorem solution :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (N : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin N → Ω → ℝ),
        (∀ i, Measurable (X i)) → iIndepFun X μ →
        (∀ i ω, X i ω = 0 ∨ X i ω = 1) →
        ∑ i, μ.real {ω | X i ω = 1} ≤ 1 →
        μ.real {ω | 3 * Real.log m / Real.log (Real.log m) < ∑ i, X i ω} ≤ 1 / (m : ℝ) ^ 2 := by
  classical
  obtain ⟨m₀,hm₀⟩ := exists_nat_gt (Real.exp 1)
  refine ⟨m₀, ?_⟩
  intro m hm N Ω _ μ _ X hmeas hind hrange hsum
  have hmexp : Real.exp 1 < (m:ℝ) := hm₀.trans_le (by exact_mod_cast hm)
  have hmpos : (0:ℝ) < m := (Real.exp_pos 1).trans hmexp
  have hlog : 1 < Real.log m := (Real.lt_log_iff_exp_lt hmpos).mpr hmexp
  have hlogpos : 0 < Real.log m := by linarith
  let t := Real.log (Real.log m)
  have ht : 0 < t := Real.log_pos hlog
  let ε := 3 * Real.log m / t
  let S := fun ω => ∑ i, X i ω
  let p := fun i => μ.real {ω | X i ω = 1}
  have hX0 : ∀ i ω, 0 ≤ X i ω := by intro i ω; rcases hrange i ω with h | h <;> simp [h]
  have hX1 : ∀ i ω, X i ω ≤ 1 := by intro i ω; rcases hrange i ω with h | h <;> simp [h]
  have hInt : ∀ i, Integrable (X i) μ := by
    intro i
    apply Integrable.of_bound (hmeas i).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 i ω)]
    exact hX1 i ω
  have hEX : ∀ i, (∫ ω, X i ω ∂μ) = p i := by
    intro i
    have he : X i = Set.indicator {ω | X i ω = 1} (fun _ => (1:ℝ)) := by
      funext ω
      rcases hrange i ω with h | h <;> simp [Set.indicator,h]
    rw [he, integral_indicator_const (1:ℝ) (measurableSet_eq_fun (hmeas i) measurable_const)]
    simp [p]
  have hp0 : ∀ i, 0 ≤ p i := by intro i; dsimp [p]; positivity
  have hcoef : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht.le)
  have hmgf : ∀ i, mgf (X i) μ t = 1 + p i * (Real.exp t - 1) := by
    intro i
    have he : (fun ω => Real.exp (t*X i ω)) = (fun ω => 1+(Real.exp t-1)*X i ω) := by
      funext ω
      rcases hrange i ω with h | h <;> simp [h] <;> ring
    unfold mgf
    rw [he, integral_add (integrable_const 1) ((hInt i).const_mul _), integral_const_mul, hEX i]
    simp
    ring
  have hmgfle : ∀ i, mgf (X i) μ t ≤ Real.exp (p i*(Real.exp t-1)) := by
    intro i
    rw [hmgf]
    simpa [add_comm] using Real.add_one_le_exp (p i*(Real.exp t-1))
  have hprod : (∏ i, mgf (X i) μ t) ≤ Real.exp (Real.exp t-1) := by
    calc
      _ ≤ ∏ i, Real.exp (p i*(Real.exp t-1)) := Finset.prod_le_prod
        (fun i hi => by rw [hmgf]; positivity) (fun i hi => hmgfle i)
      _ = Real.exp ((∑ i, p i)*(Real.exp t-1)) := by rw [← Real.exp_sum, Finset.sum_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hSmeas : Measurable S := by dsimp [S]; fun_prop
  have hSle : ∀ ω, S ω ≤ (N:ℝ) := by
    intro ω
    calc
      _ ≤ ∑ i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i hi => hX1 i ω)
      _ = _ := by simp
  have hExpInt : Integrable (fun ω => Real.exp (t*S ω)) μ := by
    apply Integrable.of_bound ((hSmeas.const_mul t).exp.aestronglyMeasurable) (Real.exp (t*N))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hSle ω) ht.le)
  have hSfun : S = ∑ i, X i := by funext ω; simp [S]
  have hmgfS : mgf S μ t = ∏ i, mgf (X i) μ t := by
    rw [hSfun]
    exact hind.mgf_sum hmeas Finset.univ
  have htail := measure_ge_le_exp_mul_mgf ε ht.le hExpInt
  rw [hmgfS] at htail
  have hbound : Real.exp (-t*ε) * Real.exp (Real.exp t-1) ≤ 1/(m:ℝ)^2 := by
    calc
      _ ≤ Real.exp (-t*ε) * Real.exp (Real.exp t) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      _ = Real.exp (-(2*Real.log m)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [t,ε]
        rw [Real.exp_log hlogpos]
        have ht0 : Real.log (Real.log (m:ℝ)) ≠ 0 := ne_of_gt ht
        field_simp [ht0]
        <;> ring
      _ = _ := by
        rw [Real.exp_neg]
        have he : Real.exp (2*Real.log m) = (m:ℝ)^2 := by
          rw [show 2*Real.log m = Real.log m+Real.log m by ring, Real.exp_add, Real.exp_log hmpos]
          ring
        rw [he, one_div]
  have hsub : μ.real {ω | ε < S ω} ≤ μ.real {ω | ε ≤ S ω} := measureReal_mono (by intro ω h; change ε ≤ S ω; change ε < S ω at h; exact h.le)
  exact hsub.trans (htail.trans ((mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le).trans hbound))
