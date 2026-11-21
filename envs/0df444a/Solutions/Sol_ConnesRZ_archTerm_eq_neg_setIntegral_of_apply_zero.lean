-- Prove2me | solution 1 for ConnesRZ.archTerm_eq_neg_setIntegral_of_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T22:33:50.347189+00:00
-- url     : https://prove2.me/submissions/93ddc275-cb3b-4bd1-a3c3-aa92554e06b3

import Definitions.Def_ConnesRZ_weil_defs
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Theorems.Thm_MasulloRH_realTraceIntegrand_integrable

set_option autoImplicit false

open Complex MeasureTheory Set ConnesRZ

/-- The multiplicative test `φ(x) = g(log x)` for `x > 0`, extended by zero. -/
noncomputable def ConnesRZ_logTest (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => if 0 < x then g (Real.log x) else 0

lemma ConnesRZ_logTest_exp (g : ℝ → ℂ) (u : ℝ) :
    ConnesRZ_logTest g (Real.exp u) = g u := by
  simp [ConnesRZ_logTest, Real.exp_pos, Real.log_exp]

/-- A compactly supported function vanishes outside some symmetric interval. -/
lemma ConnesRZ_exists_bound (g : ℝ → ℂ) (hg : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R < |x| → g x = 0 := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R 1]

lemma ConnesRZ_logTest_eq_zero_of_le (g : ℝ → ℂ) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ x : ℝ, R < |x| → g x = 0)
    (y : ℝ) (hy : y < Real.exp (-R)) : ConnesRZ_logTest g y = 0 := by
  unfold ConnesRZ_logTest
  split_ifs with hpos
  · apply hR
    have hlog : Real.log y < -R := by
      rwa [Real.log_lt_iff_lt_exp hpos]
    rw [abs_of_neg (by linarith)]
    linarith
  · rfl

lemma ConnesRZ_logTest_isRationalTraceTest (g : ℝ → ℂ) (hg : IsTest g) (hg0 : g 0 = 0) :
    MasulloRH.IsRationalTraceTest (ConnesRZ_logTest g) := by
  obtain ⟨hsmooth, hcs⟩ := hg
  obtain ⟨R, hRpos, hR⟩ := ConnesRZ_exists_bound g hcs
  have hsupp : Function.support (ConnesRZ_logTest g) ⊆ Icc (Real.exp (-R)) (Real.exp R) := by
    intro y hy
    by_contra hnot
    apply hy
    rcases not_and_or.1 hnot with h | h
    · exact ConnesRZ_logTest_eq_zero_of_le g R hRpos.le hR y (lt_of_not_ge h)
    · have hy' : Real.exp R < y := lt_of_not_ge h
      have hpos : 0 < y := lt_trans (Real.exp_pos R) hy'
      simp only [ConnesRZ_logTest, if_pos hpos]
      apply hR
      have : R < Real.log y := by rwa [Real.lt_log_iff_exp_lt hpos]
      rw [abs_of_pos (by linarith)]
      exact this
  have hts : tsupport (ConnesRZ_logTest g) ⊆ Icc (Real.exp (-R)) (Real.exp R) :=
    closure_minimal hsupp isClosed_Icc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge 0 x with hx | hx
    · have heq : ConnesRZ_logTest g =ᶠ[nhds x] fun y => g (Real.log y) := by
        filter_upwards [lt_mem_nhds hx] with y hy
        simp [ConnesRZ_logTest, hy]
      refine ContDiffAt.congr_of_eventuallyEq ?_ heq
      exact hsmooth.contDiffAt.comp x (Real.contDiffAt_log.2 hx.ne')
    · have heq : ConnesRZ_logTest g =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-R)))] with y hy
        exact ConnesRZ_logTest_eq_zero_of_le g R hRpos.le hR y hy
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  · exact hts.trans (fun y hy => lt_of_lt_of_le (Real.exp_pos _) hy.1)
  · simp [ConnesRZ_logTest, hg0]

/-- After `t = e^x`, the real trace integrand becomes the target integrand. -/
lemma ConnesRZ_realTrace_comp_exp (g : ℝ → ℂ) (x : ℝ) (hx : 0 < x) :
    Real.exp x • MasulloRH.realTraceIntegrand (ConnesRZ_logTest g) (Real.exp x) =
      (g x + g (-x)) * ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ) := by
  unfold MasulloRH.realTraceIntegrand
  rw [← Real.exp_neg, ConnesRZ_logTest_exp, ConnesRZ_logTest_exp, Complex.real_smul,
    mul_left_comm]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  set a := Real.exp (x / 2) with ha_def
  have ha : 1 < a := Real.one_lt_exp_iff.mpr (by linarith)
  have hex : Real.exp x = a ^ 2 := by rw [ha_def, ← Real.exp_nat_mul]; ring_nf
  have hsq : Real.sqrt (Real.exp x) = a := by
    rw [hex, Real.sqrt_sq (by linarith)]
  have hneg : Real.exp (-x / 2) = a⁻¹ := by rw [ha_def, ← Real.exp_neg]; ring_nf
  have hneg2 : Real.exp (-2 * x) = (a ^ 4)⁻¹ := by
    rw [ha_def, ← Real.exp_nat_mul, ← Real.exp_neg]; ring_nf
  rw [hsq, hex, hneg, hneg2]
  have ha4 : 1 < a ^ 4 := one_lt_pow₀ ha (by norm_num)
  have h4 : (a ^ 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have h5 : 1 - (a ^ 4)⁻¹ ≠ 0 := by
    have : (a ^ 4)⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha4
    linarith
  have ha0 : a ≠ 0 := by linarith
  field_simp

theorem solution (g : ℝ → ℂ) (hg : IsTest g)
    (hg0 : g 0 = 0) :
    IntegrableOn (fun x : ℝ => (g x + g (-x)) *
      ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ)) (Ioi 0) ∧
    archTerm g = -∫ x in Ioi (0 : ℝ), (g x + g (-x)) *
      ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ) := by
  set φ := ConnesRZ_logTest g with hφdef
  have hφ := ConnesRZ_logTest_isRationalTraceTest g hg hg0
  have hcomp : φ ∘ Real.exp = g := funext (ConnesRZ_logTest_exp g)
  have harch := MasulloRH.archTerm_log_test_eq_neg_real_place φ hφ
  rw [hcomp] at harch
  have hcongr : EqOn (fun x : ℝ => Real.exp x • MasulloRH.realTraceIntegrand φ (Real.exp x))
      (fun x : ℝ => (g x + g (-x)) *
        ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ)) (Ioi 0) :=
    fun x hx => ConnesRZ_realTrace_comp_exp g x hx
  have hint := MasulloRH.realTraceIntegrand_integrable φ hφ
  rw [← Real.exp_zero, ← integrableOn_comp_exp_Ioi] at hint
  refine ⟨hint.congr_fun hcongr measurableSet_Ioi, ?_⟩
  rw [harch, ← setIntegral_congr_fun measurableSet_Ioi hcongr, integral_comp_exp_Ioi,
    Real.exp_zero]
