-- Prove2me | solution 1 for BetaCoskew.ThreeMoment.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T17:24:47.747345+00:00
-- url     : https://prove2.me/submissions/b36ca8d5-1d35-4f54-b364-c67a22934277

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model
import Theorems.Thm_BetaCoskew_ThreeMoment_kernel_foc
import Theorems.Thm_BetaCoskew_ThreeMoment_eq_12
import Theorems.Thm_BetaCoskew_ThreeMoment_eq_6_7
import Theorems.Thm_BetaCoskew_ThreeMoment_eq_13
import Theorems.Thm_BetaCoskew_ThreeMoment_cov_pricing

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics BetaCoskew.ThreeMoment

/-- cov[X,Y] = E[XY] - E[X]E[Y] under L¹ hypotheses only. -/
lemma bc_cov_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    (hXY : Integrable (fun ω => X ω * Y ω) P) :
    cov[X, Y; P] = (∫ ω, X ω * Y ω ∂P) - (∫ ω, X ω ∂P) * (∫ ω, Y ω ∂P) := by
  unfold covariance
  set a := ∫ ω, X ω ∂P
  set b := ∫ ω, Y ω ∂P
  have e1 : (∫ ω, (X ω - a) * (Y ω - b) ∂P) =
      ∫ ω, (X ω * Y ω - b * X ω) - (a * Y ω - a * b) ∂P := by
    congr 1; funext ω; ring
  have e2 : (∫ ω, (X ω * Y ω - b * X ω) - (a * Y ω - a * b) ∂P) =
      (∫ ω, X ω * Y ω - b * X ω ∂P) - ∫ ω, a * Y ω - a * b ∂P :=
    integral_sub (hXY.sub (hX.const_mul b)) ((hY.const_mul a).sub (integrable_const _))
  have e3 : (∫ ω, X ω * Y ω - b * X ω ∂P) = (∫ ω, X ω * Y ω ∂P) - ∫ ω, b * X ω ∂P :=
    integral_sub hXY (hX.const_mul b)
  have e4 : (∫ ω, a * Y ω - a * b ∂P) = (∫ ω, a * Y ω ∂P) - ∫ _ω, a * b ∂P :=
    integral_sub (hY.const_mul a) (integrable_const _)
  rw [e1, e2, e3, e4, integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
  ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : Atomless P)
    (u w : ℝ → ℝ) (hu : UtilityAssumption u) (hw : WeightingAssumption w)
    (rf : ℝ) (mt : Ω → ℝ) {n : ℕ} (R : Fin n → Ω → ℝ)
    (hmkt : IsPricedMarket P mt rf R)
    (xM : Fin n → ℝ) (hxM : ∑ i, xM i = 1)
    (hEq : IsEquilibrium P u w mt (fun ω => ∑ i, xM i * R i ω))
    (hF : Continuous (cdf (P.map (fun ω => ∑ i, xM i * R i ω)))) :
    let RM : Ω → ℝ := fun ω => ∑ i, xM i * R i ω
    (mt =ᵐ[P] fun ω => mFun P u w rf RM (RM ω)) ∧
    ∀ f : ℝ → ℝ, (∀ x, 0 ≤ f x) → ContDiff ℝ 1 f →
      P.map RM = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      0 < cdf (P.map RM) 1 → cdf (P.map RM) 1 < 1 →
      ContDiffAt ℝ 3 u 1 → ContDiffAt ℝ 3 w (1 - cdf (P.map RM) 1) →
      premA P u w RM f = -(1 + rf) * deriv (mFun P u w rf RM) 1 ∧
      premB P u w RM f = -(1 + rf) * iteratedDeriv 2 (mFun P u w rf RM) 1 ∧
      (rho P u w rf RM) =o[𝓝 0] (fun x : ℝ => x ^ 2) ∧
      ∀ i, MemLp (fun ω => R i ω - 1) 2 P →
        MemLp (fun ω => RM ω - 1) 4 P →
        (∫ ω, R i ω - 1 ∂P) =
          rf + premA P u w RM f *
            cov[fun ω => R i ω - 1, fun ω => RM ω - 1; P] +
          1 / 2 * premB P u w RM f *
            cov[fun ω => R i ω - 1, fun ω => (RM ω - 1) ^ 2; P] -
          (1 + rf) *
            cov[fun ω => rho P u w rf RM (RM ω - 1),
              fun ω => R i ω - 1; P] := by
  intro RM
  -- risk-free pricing: E[mt](1+rf) = 1
  obtain ⟨i0, hi0⟩ := hmkt.riskfree
  have hrf : (∫ ω, mt ω ∂P) * (1 + rf) = 1 := by
    have h := hmkt.price i0
    rw [hi0] at h
    simpa [integral_mul_const] using h
  have hEmt_nn : 0 ≤ ∫ ω, mt ω ∂P :=
    integral_nonneg_of_ae (hmkt.pos.mono fun ω h => le_of_lt h)
  have hEmt : 0 < ∫ ω, mt ω ∂P := by
    rcases hEmt_nn.lt_or_eq with h | h
    · exact h
    · rw [← h] at hrf; simp at hrf
  have hrfpos : 0 < 1 + rf := by
    by_contra hc
    push_neg at hc
    nlinarith
  -- first-order condition and normalization
  obtain ⟨lam, hlam, hk⟩ := kernel_foc P hP u w hu hw rf mt R hmkt xM hxM hEq hF
  have hg : Integrable (fun ω =>
      deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω)) P := by
    refine (hmkt.integrable_mt.const_mul lam).congr ?_
    filter_upwards [hk] with ω hω
    rw [hω]
    field_simp
    rfl
  obtain ⟨hlamK, hm⟩ := eq_12 P u w rf mt RM lam hlam hmkt.integrable_mt hg hrf hk
  have hKpos : 0 < kernelMean P u w RM := by
    have : 0 < (1 + rf) * kernelMean P u w RM := hlamK ▸ hlam
    exact pos_of_mul_pos_right this hrfpos.le
  refine ⟨hm, ?_⟩
  intro f hf0 hfC hlaw hF0 hF1 hu3 hw3
  obtain ⟨hA, hB⟩ := eq_6_7 P u w rf RM f hf0 hfC hlaw hF0 hF1 hu3 hw3 hrfpos hKpos.ne'
  have h13 := eq_13 P u w RM f lam hlam hf0 hfC hlaw hF0 hF1 hu3 hw3
  simp only at h13
  set m := mFun P u w rf RM with hmdef
  set p0 := 1 - cdf (P.map RM) 1 with hp0
  have hK0 : kernelMean P u w RM ≠ 0 := hKpos.ne'
  -- identify the Taylor coefficients of m with c0, c1, c2 of eq_13
  have hm_eq : ∀ x, m x = lam⁻¹ * deriv w (1 - cdf (P.map RM) x) * deriv u x := by
    intro x
    rw [hmdef, mFun, hlamK]
    field_simp
  have hd1 : deriv m 1 = lam⁻¹ *
      (deriv w p0 * iteratedDeriv 2 u 1 - iteratedDeriv 2 w p0 * deriv u 1 * f 1) := by
    have h := hA
    unfold premA at h
    simp only at h
    rw [← hp0] at h
    have h' : deriv m 1 = (kernelMean P u w RM)⁻¹ *
        (deriv w p0 * iteratedDeriv 2 u 1 - iteratedDeriv 2 w p0 * deriv u 1 * f 1) /
          (1 + rf) := by
      rw [eq_div_iff hrfpos.ne']; linarith
    rw [h', hlamK]
    field_simp
  have hd2 : iteratedDeriv 2 m 1 = lam⁻¹ *
      (deriv w p0 * iteratedDeriv 3 u 1 -
        iteratedDeriv 2 w p0 * (2 * iteratedDeriv 2 u 1 * f 1 + deriv u 1 * deriv f 1) +
        iteratedDeriv 3 w p0 * deriv u 1 * f 1 ^ 2) := by
    have h := hB
    unfold premB at h
    simp only at h
    rw [← hp0] at h
    have h' : iteratedDeriv 2 m 1 = (kernelMean P u w RM)⁻¹ *
        (deriv w p0 * iteratedDeriv 3 u 1 + iteratedDeriv 3 w p0 * deriv u 1 * f 1 ^ 2 -
          iteratedDeriv 2 w p0 * (2 * iteratedDeriv 2 u 1 * f 1 + deriv u 1 * deriv f 1)) /
          (1 + rf) := by
      rw [eq_div_iff hrfpos.ne']; linarith
    rw [h', hlamK]
    field_simp
    ring
  have hrho : ∀ x, rho P u w rf RM x =
      lam⁻¹ * deriv w (1 - cdf (P.map RM) (1 + x)) * deriv u (1 + x) -
        (lam⁻¹ * (deriv w p0 * deriv u 1) +
          lam⁻¹ * (deriv w p0 * iteratedDeriv 2 u 1 -
            iteratedDeriv 2 w p0 * deriv u 1 * f 1) * x +
          lam⁻¹ * (deriv w p0 * iteratedDeriv 3 u 1 -
            iteratedDeriv 2 w p0 *
              (2 * iteratedDeriv 2 u 1 * f 1 + deriv u 1 * deriv f 1) +
            iteratedDeriv 3 w p0 * deriv u 1 * f 1 ^ 2) / 2 * x ^ 2) := by
    intro x
    unfold rho
    simp only
    rw [← hmdef, hd1, hd2, hm_eq (1 + x), hm_eq 1, hp0]
    ring
  have hrho_o : (rho P u w rf RM) =o[𝓝 0] (fun x : ℝ => x ^ 2) :=
    h13.congr (fun x => (hrho x).symm) (fun _ => rfl)
  refine ⟨hA, hB, hrho_o, ?_⟩
  -- the three-moment CAPM
  intro i hi2 hM4
  set ri : Ω → ℝ := fun ω => R i ω - 1 with hri
  set rM : Ω → ℝ := fun ω => RM ω - 1 with hrM
  have hri_int : Integrable ri P := hi2.integrable (by norm_num)
  have hrM_int : Integrable rM P := hM4.integrable (by norm_num)
  have hrM2 : MemLp rM 2 P := hM4.mono_exponent (by norm_num)
  have hrM_sq : MemLp (fun ω => rM ω ^ 2) 2 P := by
    have hmeas : AEStronglyMeasurable (fun ω => rM ω ^ 2) P :=
      hrM_int.aestronglyMeasurable.pow 2
    rw [memLp_two_iff_integrable_sq hmeas]
    have h4 := hM4.integrable_norm_pow (p := 4) (by norm_num)
    refine h4.congr (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [← pow_mul, show (2:ℕ) * 2 = 4 by norm_num, pow_abs, abs_of_nonneg (by positivity)]
  have hrM_sq_int : Integrable (fun ω => rM ω ^ 2) P := hrM_sq.integrable (by norm_num)
  have hprod1 : Integrable (fun ω => rM ω * ri ω) P := hrM2.integrable_mul hi2
  have hprod2 : Integrable (fun ω => rM ω ^ 2 * ri ω) P := hrM_sq.integrable_mul hi2
  have hmtri : Integrable (fun ω => mt ω * ri ω) P := by
    have : (fun ω => mt ω * ri ω) = fun ω => mt ω * R i ω - mt ω := by
      funext ω; simp only [hri]; ring
    rw [this]
    exact (hmkt.integrable_price i).sub hmkt.integrable_mt
  -- the kernel as a quadratic plus the Taylor remainder
  set c0 := m 1
  set c1 := deriv m 1
  set c2 := iteratedDeriv 2 m 1
  set Z : Ω → ℝ := fun ω => rho P u w rf RM (RM ω - 1) with hZ
  have hdecomp : ∀ ω, m (RM ω) = c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2 + Z ω := by
    intro ω
    simp only [hZ, hrM, rho]
    rw [← hmdef, show 1 + (RM ω - 1) = RM ω by ring]
    ring
  have hZ_ae : Z =ᵐ[P] fun ω => mt ω - (c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2) := by
    filter_upwards [hm] with ω hω
    rw [hω, hdecomp ω]
    ring
  have hpoly_int : Integrable (fun ω => c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2) P :=
    ((integrable_const c0).add (hrM_int.const_mul c1)).add (hrM_sq_int.const_mul (c2 / 2))
  have hZ_int : Integrable Z P :=
    (hmkt.integrable_mt.sub hpoly_int).congr hZ_ae.symm
  have hpolyri_int : Integrable (fun ω => (c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2) * ri ω) P := by
    have : (fun ω => (c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2) * ri ω) =
        fun ω => c0 * ri ω + c1 * (rM ω * ri ω) + c2 / 2 * (rM ω ^ 2 * ri ω) := by
      funext ω; ring
    rw [this]
    exact ((hri_int.const_mul c0).add (hprod1.const_mul c1)).add (hprod2.const_mul (c2 / 2))
  have hZri_int : Integrable (fun ω => Z ω * ri ω) P := by
    refine (hmtri.sub hpolyri_int).congr ?_
    filter_upwards [hZ_ae] with ω hω
    rw [hω]; simp only [Pi.sub_apply]; ring
  -- covariance pricing
  have hprice : (∫ ω, mt ω * (1 + ri ω) ∂P) = 1 := by
    have : (fun ω => mt ω * (1 + ri ω)) = fun ω => mt ω * R i ω := by
      funext ω; simp only [hri]; ring
    rw [this]; exact hmkt.price i
  obtain ⟨-, hcp⟩ := cov_pricing P mt ri hmkt.integrable_mt hri_int hmtri hprice hEmt
  -- expand cov[mt, ri]
  have hcov_mt : cov[mt, ri; P] =
      c1 * cov[rM, ri; P] + c2 / 2 * cov[fun ω => rM ω ^ 2, ri; P] + cov[Z, ri; P] := by
    rw [bc_cov_eq hmkt.integrable_mt hri_int hmtri, bc_cov_eq hrM_int hri_int hprod1,
      bc_cov_eq hrM_sq_int hri_int hprod2, bc_cov_eq hZ_int hri_int hZri_int]
    have hA1 : Integrable (fun ω => c0 + c1 * rM ω) P :=
      (integrable_const c0).add (hrM_int.const_mul c1)
    have hA2 : Integrable (fun ω => c2 / 2 * rM ω ^ 2) P := hrM_sq_int.const_mul (c2 / 2)
    have hB1 : Integrable (fun ω => c0 * ri ω + c1 * (rM ω * ri ω)) P :=
      (hri_int.const_mul c0).add (hprod1.const_mul c1)
    have hB2 : Integrable (fun ω => c2 / 2 * (rM ω ^ 2 * ri ω)) P := hprod2.const_mul (c2 / 2)
    have e1 : (∫ ω, mt ω ∂P) = ∫ ω, (c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2) + Z ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZ_ae] with ω hω
      rw [hω]; ring
    have e2 : (∫ ω, mt ω * ri ω ∂P) =
        ∫ ω, (c0 * ri ω + c1 * (rM ω * ri ω) + c2 / 2 * (rM ω ^ 2 * ri ω)) + Z ω * ri ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZ_ae] with ω hω
      rw [hω]; ring
    have i1 : (∫ ω, (c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2) + Z ω ∂P) =
        (∫ ω, c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2 ∂P) + ∫ ω, Z ω ∂P :=
      integral_add hpoly_int hZ_int
    have i2 : (∫ ω, c0 + c1 * rM ω + c2 / 2 * rM ω ^ 2 ∂P) =
        (∫ ω, c0 + c1 * rM ω ∂P) + ∫ ω, c2 / 2 * rM ω ^ 2 ∂P := integral_add hA1 hA2
    have i3 : (∫ ω, c0 + c1 * rM ω ∂P) = (∫ _ω, c0 ∂P) + ∫ ω, c1 * rM ω ∂P :=
      integral_add (integrable_const c0) (hrM_int.const_mul c1)
    have j1 : (∫ ω, (c0 * ri ω + c1 * (rM ω * ri ω) + c2 / 2 * (rM ω ^ 2 * ri ω)) +
        Z ω * ri ω ∂P) = (∫ ω, c0 * ri ω + c1 * (rM ω * ri ω) + c2 / 2 * (rM ω ^ 2 * ri ω) ∂P)
          + ∫ ω, Z ω * ri ω ∂P := integral_add (hB1.add hB2) hZri_int
    have j2 : (∫ ω, c0 * ri ω + c1 * (rM ω * ri ω) + c2 / 2 * (rM ω ^ 2 * ri ω) ∂P) =
        (∫ ω, c0 * ri ω + c1 * (rM ω * ri ω) ∂P) + ∫ ω, c2 / 2 * (rM ω ^ 2 * ri ω) ∂P :=
      integral_add hB1 hB2
    have j3 : (∫ ω, c0 * ri ω + c1 * (rM ω * ri ω) ∂P) =
        (∫ ω, c0 * ri ω ∂P) + ∫ ω, c1 * (rM ω * ri ω) ∂P :=
      integral_add (hri_int.const_mul c0) (hprod1.const_mul c1)
    rw [e1, e2, i1, i2, i3, j1, j2, j3]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul, smul_eq_mul,
      one_mul]
    ring
  have hEmt_val : (∫ ω, mt ω ∂P) = (1 + rf)⁻¹ := by
    field_simp; linarith
  rw [hcp, hcov_mt, hEmt_val, covariance_comm ri rM, covariance_comm ri (fun ω => rM ω ^ 2),
    hA, hB]
  field_simp
  ring
