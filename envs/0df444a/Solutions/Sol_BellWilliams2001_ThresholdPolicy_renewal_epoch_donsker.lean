-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_epoch_donsker
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:40:52.485952+00:00
-- url     : https://prove2.me/submissions/0d66bf10-1108-4adf-87df-1a12a6884429

import Theorems.Thm_DurrettProbability_donsker

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (V : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (V j)) (hind : iIndepFun V P)
    (hid : ∀ j, IdentDistrib (V j) (V 0) P P) (hLp : MemLp (V 0) 2 P)
    (hmean : ∫ ω, V 0 ω ∂P = 1) (B : ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    let a := variance (V 0) P
    (0 < a → TendstoInDistribution (fun n : ℕ =>
      DurrettProbability.walkPath (fun j ω => (V j ω - 1)/Real.sqrt a) n)
      atTop (DurrettProbability.brownianPath B) (fun _ => P) P') ∧
    (a = 0 → ∀ᵐ ω ∂P, ∀ j : ℕ, V j ω = 1) := by
  let a := variance (V 0) P
  constructor
  · intro ha
    let s := Real.sqrt a
    let W (j : ℕ) (ω : Ω) := (V j ω - 1)/s
    have hs : 0 < s := Real.sqrt_pos.2 ha
    have htrans : Measurable (fun x : ℝ => (x-1)/s) := (measurable_id.sub_const 1).div_const s
    have hW (j : ℕ) : Measurable (W j) := htrans.comp (hm j)
    have hWlaw (j : ℕ) : IdentDistrib (W j) (W 0) P P := (hid j).comp htrans
    have hWind : iIndepFun W P := hind.comp (fun _ (x:ℝ) => (x-1)/s) (fun _ => htrans)
    have hWmem : MemLp (W 0) 2 P := by
      have h := (hLp.sub (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P)).const_mul (1/s)
      convert h using 1
      funext ω
      simp [W,div_eq_mul_inv,mul_comm]
    have hWmean : ∫ ω, W 0 ω ∂P = 0 := by
      change (∫ ω, (V 0 ω-1)/s ∂P) = 0
      rw [integral_div,integral_sub (hLp.integrable one_le_two) (integrable_const 1),hmean]
      simp
    have hWvar : ∫ ω, W 0 ω^2 ∂P = 1 := by
      change (∫ ω, ((V 0 ω-1)/s)^2 ∂P) = 1
      simp_rw [div_pow]
      rw [integral_div,Real.sq_sqrt ha.le,div_eq_one_iff_eq ha.ne']
      rw [variance_eq_integral (hm 0).aemeasurable,hmean]
    exact DurrettProbability.donsker hW hWind hWlaw hWmem.integrable_sq hWmean hWvar hB hBc
  · intro ha
    have hzero : evariance (V 0) P = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).1 ha).resolve_right hLp.evariance_ne_top
    have hAE : V 0 =ᵐ[P] fun _ => 1 := by
      simpa only [hmean] using (evariance_eq_zero_iff (hm 0).aemeasurable).1 hzero
    refine ae_all_iff.2 fun j => ?_
    have hl : P.map (V 0) = Measure.dirac (1:ℝ) := by
      rw [Measure.map_congr hAE,Measure.map_const,measure_univ,one_smul]
    exact (show HasLaw (V j) (Measure.dirac (1:ℝ)) P from
      ⟨(hm j).aemeasurable,(hid j).map_eq.trans hl⟩).ae_eq_of_dirac
