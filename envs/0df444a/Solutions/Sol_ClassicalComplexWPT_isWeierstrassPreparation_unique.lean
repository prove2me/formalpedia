-- Prove2me | solution 1 for ClassicalComplexWPT.isWeierstrassPreparation_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:02.761616+00:00
-- url     : https://prove2.me/submissions/32d1632a-fc36-4045-9d33-41ecd181860d

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Theorems.Thm_ClassicalComplexWPT_constantOneSeq_apply
import Theorems.Thm_ClassicalComplexWPT_convolution_constantOneSeq
import Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_apply_fin
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_preparedTailSeq
import Theorems.Thm_ClassicalComplexWPT_eventually_norm_preparedTailSeq_lt_one
import Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_eq_iff
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_constantOneSeq
import Theorems.Thm_ClassicalComplexWPT_eval_preparedPolynomialSeq
import Theorems.Thm_ClassicalComplexWPT_seqPreparedPolynomial_unique_of_eventually_eval
import Theorems.Thm_ClassicalComplexWPT_ambient_zero_eq
import Theorems.Thm_ClassicalComplexWPT_convolution_monomialSeq
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_convolution
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_tsum
import Theorems.Thm_ClassicalComplexWPT_eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainderGlobal
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.constantOneSeq_apply
attribute [local simp] ClassicalComplexWPT.convolution_constantOneSeq
attribute [local simp] ClassicalComplexWPT.preparedTailSeq_apply_fin
attribute [local simp] ClassicalComplexWPT.seqHighShift_preparedTailSeq

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    {a a' : Fin d → Base n → ℂ} {u u' : Ambient n → ℂ}
    (h : IsWeierstrassPreparation f d a u)
    (h' : IsWeierstrassPreparation f d a' u') :
    (∀ i, a i =ᶠ[nhds 0] a' i) ∧ u =ᶠ[nhds 0] u' := by
  rcases h with ⟨ha, ha0, hu, hu0, hfu⟩
  rcases h' with ⟨ha', ha0', hu', hu0', hfu'⟩
  let v : Ambient n → ℂ := fun x ↦ u' x * (u x)⁻¹
  have hv : AnalyticAt ℂ v 0 := by
    exact hu'.mul (hu.inv hu0)
  obtain ⟨pv, hpv⟩ := hv
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hpv.radius_pos with ⟨r, hr0E, hrp⟩
  have hr0 : 0 < r := by exact_mod_cast hr0E
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  let V : Base n → L1Sequence := (weightedCoefficientSeries pv r).sum
  have hVrecon :
      (fun x : Ambient n ↦ evalL1PowerSeries (V x.1) ((r : ℂ)⁻¹ * x.2))
        =ᶠ[nhds 0] v := by
    exact eventually_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesAt
      pv r hpv hr0 hrp
  have hu_ne : ∀ᶠ x in nhds (0 : Ambient n), u x ≠ 0 :=
    hu.continuousAt.eventually_ne hu0
  have hpoly :
      (fun x : Ambient n ↦ preparedPolynomial d a x) =ᶠ[nhds 0]
        (fun x ↦ v x * preparedPolynomial d a' x) := by
    filter_upwards [hfu, hfu', hu_ne] with x hx hx' hux
    have heq : u x * preparedPolynomial d a x =
        u' x * preparedPolynomial d a' x := hx.symm.trans hx'
    dsimp only [v]
    apply (mul_left_cancel₀ hux)
    rw [heq]
    field_simp [hux]
  let S : Ambient n → Ambient n := fun x ↦ (x.1, (r : ℂ) * x.2)
  have hS : Tendsto S (nhds 0) (nhds 0) := by
    have hc : ContinuousAt S 0 := by
      dsimp only [S]
      fun_prop
    simpa [S, ambient_zero_eq] using hc.tendsto
  have hpolyS := hpoly.comp_tendsto hS
  have hVreconS := hVrecon.comp_tendsto hS
  have hpolyCurry := hpolyS.curry_nhds
  have hVCurry := hVreconS.curry_nhds
  have hsmall := eventually_norm_preparedTailSeq_lt_one r a' ha' ha0'
  have hbase : ∀ᶠ z in nhds (0 : Base n),
      preparedTailSeq r d a z = preparedTailSeq r d a' z ∧
        V z = constantOneSeq := by
    filter_upwards [hpolyCurry, hVCurry, hsmall] with z hzpoly hzV hzsmall
    have heval :
        (fun w ↦ evalL1PowerSeries
          (seqLowShift d constantOneSeq + preparedTailSeq r d a z) w) =ᶠ[nhds 0]
          (fun w ↦ evalL1PowerSeries
            (seqLowShift d (V z) + convolution (V z) (preparedTailSeq r d a' z)) w) := by
      have hunit : ∀ᶠ w : ℂ in nhds 0, ‖w‖ < 1 := by
        have hb := Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)
        filter_upwards [hb] with w hw
        simpa only [Metric.mem_ball, dist_zero_right] using hw
      filter_upwards [hzpoly, hzV, hunit] with w hwpoly hwV hw
      have hwV' : evalL1PowerSeries (V z) w = v (z, (r : ℂ) * w) := by
        simpa [V, S, hrC] using hwV
      change preparedPolynomial d a (z, (r : ℂ) * w) =
        v (z, (r : ℂ) * w) * preparedPolynomial d a' (z, (r : ℂ) * w) at hwpoly
      have hright : evalL1PowerSeries
          (seqLowShift d (V z) + convolution (V z) (preparedTailSeq r d a' z)) w =
          evalL1PowerSeries (V z) w *
            evalL1PowerSeries
              (seqLowShift d constantOneSeq + preparedTailSeq r d a' z) w := by
        rw [← evalL1PowerSeries_convolution _ _ hw]
        congr 1
        rw [convolution_add_right, seqLowShift_constantOneSeq,
          convolution_monomialSeq]
      rw [eval_preparedPolynomialSeq r hr0 a z hw,
        hright, eval_preparedPolynomialSeq r hr0 a' z hw, hwV']
      rw [hwpoly]
      ring
    exact seqPreparedPolynomial_unique_of_eventually_eval d
      (preparedTailSeq r d a z) (preparedTailSeq r d a' z) (V z)
      hzsmall (seqHighShift_preparedTailSeq r a z)
      (seqHighShift_preparedTailSeq r a' z) heval
  refine ⟨?_, ?_⟩
  · intro i
    filter_upwards [hbase] with z hz
    exact (preparedTailSeq_eq_iff hr0 a a' z).mp hz.1 i
  · have hVbase : ∀ᶠ x : Ambient n in nhds 0, V x.1 = constantOneSeq :=
      by
        have hfst : Tendsto (fun x : Ambient n ↦ x.1) (nhds 0) (nhds 0) := by
          simpa using
            (continuousAt_fst.tendsto : Tendsto (fun x : Ambient n ↦ x.1)
              (nhds 0) (nhds ((0 : Ambient n).1)))
        exact hfst.eventually (hbase.mono fun z hz ↦ hz.2)
    have hscaled : ∀ᶠ x : Ambient n in nhds 0, ‖(r : ℂ)⁻¹ * x.2‖ < 1 := by
      have hc : ContinuousAt (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2) 0 := by
        fun_prop
      have hc' : Tendsto (fun x : Ambient n ↦ (r : ℂ)⁻¹ * x.2)
          (nhds 0) (nhds 0) := by simpa [ambient_zero_eq] using hc.tendsto
      have he := hc'.eventually
        (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
      filter_upwards [he] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    filter_upwards [hVrecon, hVbase, hscaled, hu_ne] with x hxV hxone hxw hux
    have hone : evalL1PowerSeries constantOneSeq ((r : ℂ)⁻¹ * x.2) = 1 := by
      rw [evalL1PowerSeries_eq_tsum _ hxw, tsum_eq_single 0]
      · simp [constantOneSeq_apply]
      · intro k hk
        simp [constantOneSeq_apply, hk]
    have hvone : v x = 1 := by
      rw [← hxV, hxone, hone]
    dsimp only [v] at hvone
    rw [← div_eq_mul_inv] at hvone
    exact ((div_eq_one_iff_eq hux).mp hvone).symm
end ClassicalComplexWPT
