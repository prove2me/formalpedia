-- Prove2me | solution 1 for FunctionalInequalities.KLS.BorelLogConcave.exists_integrable_exp_norm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:45.441358+00:00
-- url     : https://prove2.me/submissions/4c87661f-ef90-4e16-8792-62fe99f1ef27

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments

noncomputable section
open MeasureTheory Set Topology Filter
section Moments
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
/-- A Borel log-concave probability law on a finite-dimensional space has an exponential
moment. The radius is chosen from the exhaustion by balls, the tail from Borell's lemma, and
the integral is dominated by a geometric series. -/
theorem solution {ν : ProbabilityMeasure V}
    (hν : FunctionalInequalities.KLS.BorelLogConcave ν) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun v ↦ Real.exp (t * ‖v‖)) (ν : Measure V) := by
  -- a ball of integer radius carrying mass at least 3/4
  have hmono : Monotone fun n : ℕ ↦ Metric.ball (0 : V) n := fun i j hij ↦
    Metric.ball_subset_ball (by exact_mod_cast hij)
  have htend := tendsto_measure_iUnion_atTop (μ := (ν : Measure V)) hmono
  rw [Metric.iUnion_ball_nat, measure_univ] at htend
  obtain ⟨n, hn1, hball⟩ :=
    ((eventually_ge_atTop 1).and
      (htend.eventually_const_le (ENNReal.ofReal_lt_one.mpr (by norm_num : (3 / 4 : ℝ) < 1)))).exists
  set R : ℝ := (n : ℝ) with hR_def
  have hR : 0 < R := by rw [hR_def]; exact Nat.cast_pos.mpr hn1
  have hball' : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) := hball
  have tail := hν.measure_norm_ge_le hball'
  -- the rate and the dominating series
  set t₀ : ℝ := Real.log 3 / (4 * R) with ht₀_def
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ht₀ : 0 < t₀ := by positivity
  set c : ℕ → ℝ := fun k ↦ Real.exp (t₀ * ((k : ℝ) + 1) * R) with hc_def
  set b : ℕ → ℝ := fun k ↦ (3 : ℝ) ^ ((1 - (k : ℝ)) / 2) with hb_def
  set A : ℕ → Set V := fun k ↦ {v | (k : ℝ) * R ≤ ‖v‖} with hA_def
  have hA : ∀ k, MeasurableSet (A k) := fun k ↦
    (isClosed_le continuous_const continuous_norm).measurableSet
  set f : ℕ → V → ENNReal := fun k ↦ (A k).indicator fun _ ↦ ENNReal.ofReal (c k) with hf_def
  have hc_pos : ∀ k, 0 < c k := fun k ↦ Real.exp_pos _
  have hb_pos : ∀ k, 0 < b k := fun k ↦ Real.rpow_pos_of_pos (by norm_num) _
  -- pointwise domination
  have hpt : ∀ v : V, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ∑' k, f k v := by
    intro v
    set n := ⌊‖v‖ / R⌋₊ with hn_def
    have hn1 : (n : ℝ) ≤ ‖v‖ / R := Nat.floor_le (div_nonneg (norm_nonneg _) hR.le)
    have hn2 : ‖v‖ / R < n + 1 := Nat.lt_floor_add_one _
    have hmem : v ∈ A n := by
      show (n : ℝ) * R ≤ ‖v‖
      exact (le_div_iff₀ hR).mp hn1
    have hlt : ‖v‖ < ((n : ℝ) + 1) * R := (div_lt_iff₀ hR).mp hn2
    calc ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ENNReal.ofReal (c n) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hlt.le ht₀.le
      _ = f n v := by simp [hf_def, Set.indicator_of_mem hmem]
      _ ≤ ∑' k, f k v := ENNReal.le_tsum n
  -- the series
  have hcb : ∀ k, c k * b k = (3 : ℝ) ^ ((3 : ℝ) / 4) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    intro k
    have hc : c k = (3 : ℝ) ^ (((k : ℝ) + 1) / 4) := by
      rw [hc_def, Real.rpow_def_of_pos (by norm_num)]
      rw [ht₀_def]
      field_simp
    rw [hc, hb_def]
    simp only
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hq1 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable fun k ↦ c k * b k :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _).congr fun k ↦ (hcb k).symm
  -- the integral bound
  have hbound : ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V) < ⊤ := by
    calc ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V)
        ≤ ∫⁻ v, ∑' k, f k v ∂(ν : Measure V) := lintegral_mono hpt
      _ = ∑' k, ∫⁻ v, f k v ∂(ν : Measure V) :=
          lintegral_tsum fun k ↦ (measurable_const.indicator (hA k)).aemeasurable
      _ = ∑' k, ENNReal.ofReal (c k) * (ν : Measure V) (A k) := by
          congr 1; ext k; exact lintegral_indicator_const (hA k) _
      _ ≤ ∑' k, ENNReal.ofReal (c k) * ENNReal.ofReal (b k) :=
          ENNReal.tsum_le_tsum fun k ↦ mul_le_mul' le_rfl (tail k)
      _ = ∑' k, ENNReal.ofReal (c k * b k) := by
          congr 1; ext k; rw [ENNReal.ofReal_mul (hc_pos k).le]
      _ = ENNReal.ofReal (∑' k, c k * b k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (mul_pos (hc_pos k) (hb_pos k)).le) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨t₀, ht₀, ?_, ?_⟩
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
      |>.aestronglyMeasurable
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v ↦ (Real.exp_pos _).le)]
    exact hbound
