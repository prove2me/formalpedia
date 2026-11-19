-- Prove2me | solution 1 for BilateralProfitMHR.claim_5_5
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T11:41:04.233073+00:00
-- url     : https://prove2.me/submissions/ce7b8a23-ccdc-4f3e-862c-a3e6f2e3d70d

import Mathlib
import Definitions.Def_BilateralProfitMHR_LogProfitOracle
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2


namespace BilateralProfitMHR

open MeasureTheory
open scoped ENNReal

private theorem geomLaw_probability (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    IsProbabilityMeasure (geomLaw Q) := by
  have hs := (hasSum_geometric_of_lt_one (sub_nonneg.mpr hQ1)
    (sub_lt_self 1 hQ0)).mul_right Q
  have hs' : HasSum (fun k : ℕ => (1 - Q) ^ k * Q) 1 := by
    simpa only [show 1 - (1 - Q) = Q by ring, inv_mul_cancel₀ hQ0.ne'] using hs
  exact hs'.isProbabilityMeasure_sum_dirac (fun k => by positivity)

private theorem geomLaw_singleton_zero (Q : ℝ) : geomLaw Q {0} = 0 := by
  simp [geomLaw, Measure.sum_apply_of_countable, Measure.dirac_apply']

private theorem geomLaw_singleton_succ (Q : ℝ) (k : ℕ) :
    geomLaw Q {k + 1} = ENNReal.ofReal ((1 - Q) ^ k * Q) := by
  simp only [geomLaw, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [tsum_eq_single k]
  · simp
  · intro j hj
    simp [Set.indicator_apply, hj]

private theorem harm_nonneg (m : ℕ) : 0 ≤ harm m := by
  unfold harm
  exact Finset.sum_nonneg fun k _ => by positivity

private theorem harm_le_nat (m : ℕ) : harm m ≤ (m : ℝ) := by
  unfold harm
  calc
    _ ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      apply div_le_one_of_le₀
      · have := Nat.cast_nonneg (α := ℝ) k
        linarith
      · positivity
    _ = m := by simp

private theorem harm_succ (m : ℕ) : harm (m + 1) = harm m + 1 / ((m : ℝ) + 1) := by
  simp [harm, Finset.sum_range_succ]

private theorem geom_harm_summable (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Summable (fun k : ℕ => (1 - Q) ^ k * harm k) := by
  have hr : ‖1 - Q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hQ1)]
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (harm_nonneg k))
      (fun k => ?_) (by simpa [pow_one] using hs)
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (harm_le_nat k)
    (pow_nonneg (sub_nonneg.mpr hQ1) k)

private theorem geomLaw_harm_integrable (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Integrable (fun N : ℕ => harm (N - 1)) (geomLaw Q) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [Nat.add_sub_cancel, ENNReal.toReal_ofReal (mul_nonneg
    (pow_nonneg (sub_nonneg.mpr hQ1) _) hQ0.le), Real.norm_eq_abs,
    abs_of_nonneg (harm_nonneg _), mul_right_comm] using
    (geom_harm_summable Q hQ0 hQ1).mul_right Q

private theorem geomLaw_harm_mean (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    ∫ N, harm (N - 1) ∂(geomLaw Q) = -Real.log Q := by
  have hs := geom_harm_summable Q hQ0 hQ1
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |1 - Q| < 1 by rw [abs_of_nonneg (sub_nonneg.mpr hQ1)]; linarith)
  rw [show 1 - (1 - Q) = Q by ring] at hlog
  have hrec : ∀ k : ℕ, (1 - Q) ^ (k + 1) * harm (k + 1) =
      (1 - Q) * ((1 - Q) ^ k * harm k) +
        (1 - Q) ^ (k + 1) / ((k : ℝ) + 1) := by
    intro k
    rw [harm_succ, pow_succ]
    ring
  have hsum : (∑' k : ℕ, (1 - Q) ^ k * harm k) =
      (1 - Q) * (∑' k : ℕ, (1 - Q) ^ k * harm k) - Real.log Q := by
    calc
      _ = ∑' k : ℕ, (1 - Q) ^ (k + 1) * harm (k + 1) := by
        simpa [harm] using (hs.tsum_eq_zero_add (f := fun k : ℕ => (1 - Q) ^ k * harm k))
      _ = (1 - Q) * (∑' k : ℕ, (1 - Q) ^ k * harm k) - Real.log Q := by
        simp_rw [hrec]
        rw [Summable.tsum_add (hs.mul_left (1 - Q))
          (by simpa only [Nat.cast_add, Nat.cast_one] using hlog.summable),
          tsum_mul_left]
        simpa only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg] using
          congrArg ((1 - Q) * (∑' k : ℕ, (1 - Q) ^ k * harm k) + ·) hlog.tsum_eq
  unfold geomLaw
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  simp only [Nat.add_sub_cancel, ENNReal.toReal_ofReal (mul_nonneg
    (pow_nonneg (sub_nonneg.mpr hQ1) _) hQ0.le), smul_eq_mul]
  simp_rw [mul_right_comm _ Q]
  rw [tsum_mul_right]
  nlinarith

private theorem geomLaw_wait_integrable (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Integrable (fun N : ℕ => (N : ℝ)) (geomLaw Q) := by
  have hr : ‖1 - Q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hQ1)]
    linarith
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.add
    (summable_geometric_of_norm_lt_one hr)
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  convert! hs.mul_right Q using 1
  ext k
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) + 1)]
  ring

private theorem geomLaw_wait_mean (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    ∫ N, (N : ℝ) ∂(geomLaw Q) = 1 / Q := by
  have hr : ‖1 - Q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hQ1)]
    linarith
  have hs := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    (hasSum_geometric_of_norm_lt_one hr)).mul_right Q
  have hs' : HasSum (fun k : ℕ => ((1 - Q) ^ k * Q) * ((k + 1 : ℕ) : ℝ))
      (1 / Q) := by
    convert! hs using 1
    · ext k
      push_cast
      ring
    · rw [show 1 - (1 - Q) = Q by ring]
      field_simp
      ring
  unfold geomLaw
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  simpa only [ENNReal.toReal_ofReal (mul_nonneg
    (pow_nonneg (sub_nonneg.mpr hQ1) _) hQ0.le), smul_eq_mul] using hs'.tsum_eq

private theorem Ptrade_measurable (D : Measure (ℝ × ℝ)) [SFinite D] :
    Measurable (BilateralProfit.Ptrade D) := by
  unfold BilateralProfit.Ptrade
  exact (measurable_measure_prodMk_left
    (show MeasurableSet {w : (ℝ × ℝ) × (ℝ × ℝ) |
      BilateralProfit.Trades w.2 w.1} by
        unfold BilateralProfit.Trades
        exact (measurableSet_le (by fun_prop : Measurable (fun w :
          (ℝ × ℝ) × (ℝ × ℝ) => w.2.1)) (by fun_prop)).inter
          (measurableSet_le (by fun_prop : Measurable (fun w :
            (ℝ × ℝ) × (ℝ × ℝ) => w.1.2)) (by fun_prop)))).ennreal_toReal

private theorem oracleLaw_measurable (D : Measure (ℝ × ℝ)) [SFinite D] :
    Measurable (oracleLaw D) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hg : ∀ x : ℝ × ℝ, Measurable (fun N : ℕ =>
      harm (N - 1) - Real.log (x.2 - x.1)) := fun _ => measurable_of_countable _
  simp only [oracleLaw, Measure.map_apply (hg _) hs, geomLaw,
    Measure.sum_apply _ (hg _ hs), Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hg _ hs)]
  apply Measurable.tsum
  intro k
  apply Measurable.mul
  · exact ENNReal.measurable_ofReal.comp
      (((measurable_const.sub (Ptrade_measurable D)).pow_const k).mul (Ptrade_measurable D))
  · exact measurable_const.indicator (hs.preimage (by fun_prop : Measurable (fun x : ℝ × ℝ =>
      harm (k + 1 - 1) - Real.log (x.2 - x.1))))

end BilateralProfitMHR


namespace BilateralProfitMHR

open MeasureTheory Set
open scoped ENNReal

private theorem enn_tsum_succ (f : ℕ → ℝ≥0∞) :
    (∑' k, f k) = f 0 + ∑' k, f (k + 1) := tsum_eq_zero_add' ENNReal.summable

private theorem harm_eq_harmonic (n : ℕ) : harm n = (harmonic n : ℝ) := by
  simp [harm, harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]

private theorem log_succ_le_harm (n : ℕ) : Real.log (n + 1) ≤ harm n := by
  simpa only [harm_eq_harmonic, Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n

private theorem harm_le_one_log_succ (n : ℕ) : harm n ≤ 1 + Real.log (n + 1) := by
  rcases n with _ | n
  · norm_num [harm]
  rw [harm_eq_harmonic]
  apply (harmonic_le_one_add_log (n + 1)).trans
  have hl : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  exact add_le_add_right hl 1

private theorem geomLaw_tail (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) (m : ℕ) :
    geomLaw Q {N : ℕ | m < N} = ENNReal.ofReal ((1 - Q) ^ m) := by
  have hQ : 0 ≤ 1 - Q := sub_nonneg.mpr hQ1
  have heq (j : ℕ) : geomLaw Q {N : ℕ | j < N} =
      ∑' k : ℕ, ENNReal.ofReal ((1 - Q) ^ k * Q) *
        (if j < k + 1 then 1 else 0) := by
    simp only [geomLaw, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
      Set.mem_setOf_eq, Set.indicator_apply, Pi.one_apply]
  induction m with
  | zero =>
      haveI := geomLaw_probability Q hQ0 hQ1
      rw [heq]
      simp only [Nat.zero_lt_succ, if_true, mul_one, pow_zero, ENNReal.ofReal_one]
      have hs := (hasSum_geometric_of_lt_one hQ (by linarith : 1 - Q < 1)).mul_right Q
      have hs' : HasSum (fun k : ℕ => (1 - Q) ^ k * Q) 1 := by
        simpa only [show 1 - (1 - Q) = Q by ring, inv_mul_cancel₀ hQ0.ne'] using hs
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs'.summable).symm.trans
          (congrArg ENNReal.ofReal hs'.tsum_eq)
  | succ m ih =>
      rw [heq]
      have hs : (∑' k : ℕ, ENNReal.ofReal ((1 - Q) ^ k * Q) *
          (if m + 1 < k + 1 then 1 else 0)) =
        ENNReal.ofReal ((1 - Q) ^ 0 * Q) * (if m + 1 < 0 + 1 then 1 else 0) +
        ∑' k : ℕ, ENNReal.ofReal ((1 - Q) ^ (k + 1) * Q) *
          (if m + 1 < k + 1 + 1 then 1 else 0) := by
        exact enn_tsum_succ _
      rw [hs]
      simp only [Nat.add_lt_add_iff_right, Nat.succ_eq_add_one,
        show ¬m + 1 < 0 + 1 by omega, if_false, mul_zero, zero_add]
      calc
        _ = ENNReal.ofReal (1 - Q) *
            (∑' k : ℕ, ENNReal.ofReal ((1 - Q) ^ k * Q) *
              (if m < k + 1 then 1 else 0)) := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro k
          rw [show (1 - Q) ^ (k + 1) * Q = (1 - Q) * ((1 - Q) ^ k * Q) by ring,
            ENNReal.ofReal_mul hQ]
          simp only [Nat.add_lt_add_iff_right, mul_assoc]
        _ = _ := by
          rw [← heq, ih, ← ENNReal.ofReal_mul hQ]
          congr 1
          ring

private theorem geomLaw_cdf_le (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) (m : ℕ) :
    geomLaw Q {N : ℕ | N ≤ m} ≤ ENNReal.ofReal (Q * m) := by
  haveI := geomLaw_probability Q hQ0 hQ1
  have heq : {N : ℕ | N ≤ m} = {N : ℕ | m < N}ᶜ := by ext N; simp
  rw [heq, measure_compl (Set.to_countable _).measurableSet (by exact measure_ne_top _ _),
    measure_univ, geomLaw_tail Q hQ0 hQ1]
  have hpow : (1 - Q) ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hbern : 1 - Q * (m : ℝ) ≤ (1 - Q) ^ m := by
    clear heq hpow
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        have hm := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 - Q)
        nlinarith [mul_nonneg hQ0.le (Nat.cast_nonneg (α := ℝ) m)]
  linarith

private theorem exp_upper_square (u : ℝ) (hu : 2 ≤ u) : u ^ 2 / 4 ≤ Real.exp (u - 1) - 1 := by
  have he := Real.sum_le_exp_of_nonneg (show 0 ≤ u - 1 by linarith) 3
  norm_num [Finset.sum_range_succ] at he
  nlinarith

private theorem geom_harm_upper_tail (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (u : ℝ) (hu : 2 ≤ u) :
    geomLaw Q {N : ℕ | u < harm (N - 1) + Real.log Q} ≤
      ENNReal.ofReal (Real.exp (-u ^ 2 / 4)) := by
  have hlogQ : Real.log Q ≤ 0 := Real.log_nonpos hQ0.le hQ1
  let t := Real.exp (u - 1) / Q
  have ht0 : 0 < t := div_pos (Real.exp_pos _) hQ0
  have hsub : {N : ℕ | u < harm (N - 1) + Real.log Q} ⊆ {N : ℕ | ⌊t⌋₊ < N} := by
    intro N hN
    change u < harm (N - 1) + Real.log Q at hN
    change ⌊t⌋₊ < N
    apply (Nat.floor_lt ht0.le).mpr
    rcases N with _ | N
    · simp only [Nat.zero_sub, harm, Finset.sum_range_zero] at hN
      norm_num at hN
      linarith
    have hH := harm_le_one_log_succ N
    have hlt : u - 1 < Real.log (((N + 1 : ℕ) : ℝ) * Q) := by
      rw [Real.log_mul (by positivity) hQ0.ne']
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hN ⊢
      linarith
    have he := Real.exp_lt_exp.mpr hlt
    rw [Real.exp_log (by positivity)] at he
    exact (div_lt_iff₀ hQ0).mpr he
  refine (measure_mono hsub).trans ?_
  rw [geomLaw_tail Q hQ0 hQ1]
  apply ENNReal.ofReal_le_ofReal
  calc
    (1 - Q) ^ ⌊t⌋₊ ≤ Real.exp (-Q) ^ ⌊t⌋₊ :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg Q) _
    _ = Real.exp (-Q * (⌊t⌋₊ : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (Q - Real.exp (u - 1)) := by
      apply Real.exp_le_exp.mpr
      have hf := Nat.sub_one_lt_floor t
      have ht : Q * t = Real.exp (u - 1) := by dsimp [t]; field_simp
      nlinarith
    _ ≤ Real.exp (-u ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have he := exp_upper_square u hu
      linarith

private theorem geom_harm_lower_tail_raw (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (u : ℝ) :
    geomLaw Q {N : ℕ | harm (N - 1) + Real.log Q < -u} ≤
      ENNReal.ofReal (Real.exp (-u)) := by
  let t := Real.exp (-u) / Q
  have ht0 : 0 < t := div_pos (Real.exp_pos _) hQ0
  have hsub : {N : ℕ | harm (N - 1) + Real.log Q < -u} ⊆ {N : ℕ | N ≤ ⌊t⌋₊} := by
    intro N hN
    change harm (N - 1) + Real.log Q < -u at hN
    change N ≤ ⌊t⌋₊
    apply Nat.le_floor
    rcases N with _ | N
    · simpa only [Nat.cast_zero] using ht0.le
    have hH := log_succ_le_harm N
    have hlt : Real.log (((N + 1 : ℕ) : ℝ) * Q) < -u := by
      rw [Real.log_mul (by positivity) hQ0.ne']
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hN ⊢
      linarith
    have he := Real.exp_lt_exp.mpr hlt
    rw [Real.exp_log (by positivity)] at he
    exact ((lt_div_iff₀ hQ0).mpr he).le
  refine (measure_mono hsub).trans ((geomLaw_cdf_le Q hQ0 hQ1 ⌊t⌋₊).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hf := mul_le_mul_of_nonneg_left (Nat.floor_le ht0.le) hQ0.le
  have ht : Q * t = Real.exp (-u) := by dsimp [t]; field_simp
  linarith

private theorem geom_harm_lower_tail (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (u : ℝ) (hu : 0 ≤ u) :
    geomLaw Q {N : ℕ | harm (N - 1) + Real.log Q < -u} ≤
      ENNReal.ofReal (Real.exp (-u ^ 2 / (1 - Real.log Q))) := by
  have hlogQ : Real.log Q ≤ 0 := Real.log_nonpos hQ0.le hQ1
  have ha : 0 < 1 - Real.log Q := by linarith
  by_cases hcut : u ≤ -Real.log Q
  · refine (geom_harm_lower_tail_raw Q hQ0 hQ1 u).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ ha).mpr
    nlinarith
  · have hempty : {N : ℕ | harm (N - 1) + Real.log Q < -u} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro N hN
      change harm (N - 1) + Real.log Q < -u at hN
      have := harm_nonneg (N - 1)
      linarith
    rw [hempty, measure_empty]
    exact bot_le

private theorem geom_harm_absolute_tail (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (u : ℝ) (hu : 0 ≤ u) :
    geomLaw Q {N : ℕ | u < |harm (N - 1) + Real.log Q|} ≤
      ENNReal.ofReal (3 * Real.exp (-u ^ 2 / (4 * (1 - Real.log Q)))) := by
  haveI := geomLaw_probability Q hQ0 hQ1
  let a := 1 - Real.log Q
  have ha1 : 1 ≤ a := by dsimp [a]; linarith [Real.log_nonpos hQ0.le hQ1]
  have ha : 0 < a := by linarith
  by_cases hu2 : 2 ≤ u
  · have heq : {N : ℕ | u < |harm (N - 1) + Real.log Q|} =
        {N : ℕ | u < harm (N - 1) + Real.log Q} ∪
        {N : ℕ | harm (N - 1) + Real.log Q < -u} := by
      ext N
      simp only [mem_setOf_eq, mem_union, lt_abs]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by linarith)
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (by linarith)
    have hup : Real.exp (-u ^ 2 / 4) ≤ Real.exp (-u ^ 2 / (4 * a)) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity)).mpr
      nlinarith [sq_nonneg u]
    have hlo : Real.exp (-u ^ 2 / a) ≤ Real.exp (-u ^ 2 / (4 * a)) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ ha (by positivity)).mpr
      nlinarith [sq_nonneg u]
    calc
      _ ≤ geomLaw Q {N : ℕ | u < harm (N - 1) + Real.log Q} +
          geomLaw Q {N : ℕ | harm (N - 1) + Real.log Q < -u} := by
        rw [heq]
        exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 4)) +
          ENNReal.ofReal (Real.exp (-u ^ 2 / a)) :=
        add_le_add (geom_harm_upper_tail Q hQ0 hQ1 u hu2)
          (geom_harm_lower_tail Q hQ0 hQ1 u hu)
      _ ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / (4 * a))) +
          ENNReal.ofReal (Real.exp (-u ^ 2 / (4 * a))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlo)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        dsimp [a]
        nlinarith [Real.exp_pos (-u ^ 2 / (4 * (1 - Real.log Q)))]
  · have hb : -1 ≤ -u ^ 2 / (4 * a) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have he : 1 ≤ 3 * Real.exp (-1) := by
      rw [Real.exp_neg]
      change 1 ≤ 3 / Real.exp 1
      exact (le_div_iff₀ (Real.exp_pos 1)).mpr (by simpa using Real.exp_one_lt_three.le)
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (3 * Real.exp (-1)) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hb) (by norm_num))

end BilateralProfitMHR


namespace BilateralProfitMHR

open MeasureTheory Set
open scoped ENNReal

private theorem moment_of_power_tail {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {ω | t < f ω} ≤ ENNReal.ofReal (3 * t ^ (-4 : ℝ))) :
    Integrable f μ ∧ ∫ ω, f ω ∂μ ≤ 2 := by
  have hI : (Ioi (0 : ℝ)) = Ioc 0 1 ∪ Ioi 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    grind
  have hbound : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ 2 := by
    rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hf0) hf.aemeasurable, hI,
      lintegral_union measurableSet_Ioi (by exact disjoint_left.mpr fun x hx hy => (not_lt_of_ge hx.2) hy)]
    have hlo : ∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < f ω} ≤ 1 := by
      calc
        _ ≤ ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) :=
          lintegral_mono fun _ => prob_le_one
        _ = 1 := by simp
    have hhi : ∫⁻ t in Ioi (1 : ℝ), μ {ω | t < f ω} ≤ 1 := by
      calc
        _ ≤ ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (3 * t ^ (-4 : ℝ)) := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro t ht
          exact htail t ht.le
        _ = 1 := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1)
              (by norm_num : (0 : ℝ) < 1)]
            norm_num
          · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1)
              (by norm_num : (0 : ℝ) < 1)).const_mul 3
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht' : 1 < t := ht
            exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
    exact (add_le_add hlo hhi).trans_eq (by norm_num)
  have hint : Integrable f μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    change (∫⁻ ω, ‖f ω‖ₑ ∂μ) < ⊤
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 _)] using
      hbound.trans_lt (by norm_num : (2 : ℝ≥0∞) < ⊤)
  refine ⟨hint, ?_⟩
  have heq := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)
  rw [← heq] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp (by simpa using hbound)

private theorem subgaussianNorm_of_gaussian_tail {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (a : ℝ) (ha : 0 < a)
    (htail : ∀ u : ℝ, 0 ≤ u → μ {ω | u < |X ω|} ≤
      ENNReal.ofReal (3 * Real.exp (-u ^ 2 / (4 * a)))) :
    HighDimProb.Concentration.subgaussianNorm μ X ≤
      ENNReal.ofReal (4 * Real.sqrt a) := by
  have hpow : (4 * Real.sqrt a) ^ 2 = 16 * a := by
    nlinarith [Real.sq_sqrt ha.le]
  have hm := moment_of_power_tail μ (fun ω => Real.exp ((X ω) ^ 2 / (16 * a)))
    (by fun_prop) (fun _ => (Real.exp_pos _).le) ?_
  · unfold HighDimProb.Concentration.subgaussianNorm
    refine iInf_le_of_le (4 * Real.sqrt a) (iInf_le_of_le (by positivity) ?_)
    rw [hpow]
    exact iInf_le_of_le hm.1 (iInf_le_of_le hm.2 le_rfl)
  · intro t ht
    have ht0 : 0 < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    let u := Real.sqrt (16 * a * Real.log t)
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = 16 * a * Real.log t := Real.sq_sqrt (by positivity)
    have hsub : {ω | t < Real.exp ((X ω) ^ 2 / (16 * a))} ⊆
        {ω | u < |X ω|} := by
      intro ω hω
      have hlt := (Real.log_lt_iff_lt_exp ht0).mpr hω
      have hlt' := (lt_div_iff₀ (show 0 < 16 * a by positivity)).mp hlt
      have habs : 0 ≤ |X ω| := abs_nonneg _
      have hs : |X ω| ^ 2 = (X ω) ^ 2 := sq_abs _
      change u < |X ω|
      nlinarith
    refine (measure_mono hsub).trans ((htail u hu0).trans_eq ?_)
    congr 1
    rw [Real.rpow_def_of_pos ht0, hu2]
    congr 2
    field_simp
    ring

end BilateralProfitMHR


namespace BilateralProfitMHR

open MeasureTheory

theorem claim_5_5 (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Integrable (fun N : ℕ => harm (N - 1)) (geomLaw Q) ∧
      ∫ N, harm (N - 1) ∂(geomLaw Q) = -Real.log Q ∧
      HighDimProb.Concentration.subgaussianNorm (geomLaw Q)
          (fun N : ℕ => harm (N - 1) + Real.log Q) ≤
        ENNReal.ofReal (4 * Real.sqrt (1 - Real.log Q)) := by
  haveI := geomLaw_probability Q hQ0 hQ1
  refine ⟨geomLaw_harm_integrable Q hQ0 hQ1, geomLaw_harm_mean Q hQ0 hQ1, ?_⟩
  exact subgaussianNorm_of_gaussian_tail (geomLaw Q) _ (measurable_of_countable _)
    (1 - Real.log Q) (by linarith [Real.log_nonpos hQ0.le hQ1])
    (geom_harm_absolute_tail Q hQ0 hQ1)


end BilateralProfitMHR

open BilateralProfitMHR MeasureTheory

theorem solution (Q : ℝ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) :
    Integrable (fun N : ℕ => harm (N - 1)) (geomLaw Q) ∧
      ∫ N, harm (N - 1) ∂(geomLaw Q) = -Real.log Q ∧
      HighDimProb.Concentration.subgaussianNorm (geomLaw Q)
          (fun N : ℕ => harm (N - 1) + Real.log Q) ≤
        ENNReal.ofReal (4 * Real.sqrt (1 - Real.log Q)) := BilateralProfitMHR.claim_5_5 Q hQ0 hQ1
