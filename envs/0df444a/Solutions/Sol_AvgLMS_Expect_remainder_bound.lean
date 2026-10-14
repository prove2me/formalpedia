-- Prove2me | solution 1 for AvgLMS.Expect.remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:50:01.815413+00:00
-- url     : https://prove2.me/submissions/e4bf4727-1ffe-4aaf-baef-7b4b58028388

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMSRB

open AvgLMS.Expect

theorem q_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (v : Hs d) :
    ⟪v, H v⟫_ℝ = ∫ ω, ⟪x 1 ω, v⟫_ℝ ^ 2 ∂μ := by
  rw [hA.cov_eq v v]; congr 1; funext ω; ring

theorem q_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (v : Hs d) :
    0 ≤ ⟪v, H v⟫_ℝ := by
  rw [q_eq hA]; exact integral_nonneg fun _ => sq_nonneg _

theorem int_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (v : Hs d) :
    Integrable (fun ω => ⟪x 1 ω, v⟫_ℝ ^ 2) μ :=
  (hA.integrable_cov v v).congr (Filter.Eventually.of_forall fun ω => by dsimp only; ring)

theorem H_symm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (u w : Hs d) :
    ⟪H u, w⟫_ℝ = ⟪u, H w⟫_ℝ := by
  rw [real_inner_comm w (H u), hA.cov_eq w u, hA.cov_eq u w]
  congr 1; funext ω; ring

/-- `E‖x‖² ≤ R²`. -/
theorem norm_sq_x {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) :
    Integrable (fun ω => ‖x 1 ω‖ ^ 2) μ ∧ ∫ ω, ‖x 1 ω‖ ^ 2 ∂μ ≤ R ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hsum : ∀ y : Hs d, ‖y‖ ^ 2 = ∑ i, ⟪y, b i⟫_ℝ ^ 2 := by
    intro y
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner y y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm y (b i)]; ring
  have i2 : Integrable (fun ω => ‖x 1 ω‖ ^ 2) μ := by
    have : (fun ω => ‖x 1 ω‖ ^ 2) = fun ω => ∑ i, ⟪x 1 ω, b i⟫_ℝ ^ 2 := by
      funext ω; rw [hsum]
    rw [this]; exact integrable_finsetSum _ fun i _ => int_sq hA (b i)
  have i4 : Integrable (fun ω => ‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2) μ := by
    have : (fun ω => ‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2) =
        fun ω => ∑ i, ‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b i⟫_ℝ ^ 2 := by
      funext ω; rw [← Finset.mul_sum, ← hsum]
    rw [this]
    exact integrable_finsetSum _ fun i _ => hA.integrable_fourth (b i)
  have h4 : ∫ ω, ‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2 ∂μ ≤ R ^ 2 * ∫ ω, ‖x 1 ω‖ ^ 2 ∂μ := by
    have e1 : (fun ω => ‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2) =
        fun ω => ∑ i, ‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b i⟫_ℝ ^ 2 := by
      funext ω; rw [← Finset.mul_sum, ← hsum]
    have e2 : (fun ω => ‖x 1 ω‖ ^ 2) = fun ω => ∑ i, ⟪x 1 ω, b i⟫_ℝ ^ 2 := by
      funext ω; rw [hsum]
    rw [e1, e2, integral_finsetSum _ fun i _ => hA.integrable_fourth (b i),
      integral_finsetSum _ fun i _ => int_sq hA (b i), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← q_eq hA]
    exact hA.fourth_le (b i)
  refine ⟨i2, ?_⟩
  set m := ∫ ω, ‖x 1 ω‖ ^ 2 ∂μ with hm
  have hR := hA.R_pos
  have hR2 : 0 < R ^ 2 := by positivity
  -- pointwise AM-GM: R² ‖x‖² ≤ (‖x‖⁴ + R⁴) / 2
  have hpt : ∀ ω, R ^ 2 * ‖x 1 ω‖ ^ 2 ≤ (‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2 + R ^ 2 * R ^ 2) / 2 := by
    intro ω; nlinarith [sq_nonneg (‖x 1 ω‖ ^ 2 - R ^ 2)]
  have hint : R ^ 2 * m ≤ (∫ ω, ‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2 ∂μ + R ^ 2 * R ^ 2) / 2 := by
    rw [hm, ← integral_const_mul]
    have hi := integral_mono (f := fun ω => R ^ 2 * ‖x 1 ω‖ ^ 2)
      (g := fun ω => (‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2 + R ^ 2 * R ^ 2) / 2)
      (i2.const_mul (R ^ 2)) ((i4.add (integrable_const (R ^ 2 * R ^ 2))).div_const 2) hpt
    have e3 : ∫ ω, (‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2 + R ^ 2 * R ^ 2) / 2 ∂μ =
        (∫ ω, ‖x 1 ω‖ ^ 2 * ‖x 1 ω‖ ^ 2 ∂μ + R ^ 2 * R ^ 2) / 2 := by
      rw [integral_div, integral_add i4 (integrable_const _), integral_const]; simp
    rw [e3] at hi; exact hi
  nlinarith

/-- `q(w) ≤ R² ‖w‖²`. -/
theorem q_le_norm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (w : Hs d) :
    ⟪w, H w⟫_ℝ ≤ R ^ 2 * ‖w‖ ^ 2 := by
  obtain ⟨i2, h2⟩ := norm_sq_x hA
  rw [q_eq hA]
  have hpt : ∀ ω, ⟪x 1 ω, w⟫_ℝ ^ 2 ≤ ‖w‖ ^ 2 * ‖x 1 ω‖ ^ 2 := by
    intro ω
    have := abs_real_inner_le_norm (x 1 ω) w
    have h0 : 0 ≤ |⟪x 1 ω, w⟫_ℝ| := abs_nonneg _
    rw [← sq_abs]; nlinarith [norm_nonneg (x 1 ω), norm_nonneg w]
  calc ∫ ω, ⟪x 1 ω, w⟫_ℝ ^ 2 ∂μ ≤ ∫ ω, ‖w‖ ^ 2 * ‖x 1 ω‖ ^ 2 ∂μ :=
        integral_mono (int_sq hA w) (i2.const_mul _) hpt
    _ = ‖w‖ ^ 2 * ∫ ω, ‖x 1 ω‖ ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ ‖w‖ ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = R ^ 2 * ‖w‖ ^ 2 := by ring

/-- `‖H v‖² ≤ R² q(v)`. -/
theorem normH_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (v : Hs d) :
    ‖H v‖ ^ 2 ≤ R ^ 2 * ⟪v, H v⟫_ℝ := by
  set w := H v with hw
  have hR := hA.R_pos
  have hR2 : 0 < R ^ 2 := by positivity
  have e : ‖w‖ ^ 2 = ∫ ω, ⟪x 1 ω, w⟫_ℝ * ⟪x 1 ω, v⟫_ℝ ∂μ := by
    rw [← hA.cov_eq w v, real_inner_self_eq_norm_sq]
  -- AM-GM with weight R²: 2 a b ≤ a²/R² + R² b²
  have hpt : ∀ ω, ⟪x 1 ω, w⟫_ℝ * ⟪x 1 ω, v⟫_ℝ ≤
      (⟪x 1 ω, w⟫_ℝ ^ 2 / R ^ 2 + R ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2) / 2 := by
    intro ω
    have := sq_nonneg (⟪x 1 ω, w⟫_ℝ / R - R * ⟪x 1 ω, v⟫_ℝ)
    have hR0 : R ≠ 0 := hR.ne'
    have e2 : (⟪x 1 ω, w⟫_ℝ / R - R * ⟪x 1 ω, v⟫_ℝ) ^ 2 =
        ⟪x 1 ω, w⟫_ℝ ^ 2 / R ^ 2 + R ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 - 2 * (⟪x 1 ω, w⟫_ℝ * ⟪x 1 ω, v⟫_ℝ) := by
      field_simp; ring
    linarith
  have hI : ∫ ω, ⟪x 1 ω, w⟫_ℝ * ⟪x 1 ω, v⟫_ℝ ∂μ ≤
      (⟪w, H w⟫_ℝ / R ^ 2 + R ^ 2 * ⟪v, H v⟫_ℝ) / 2 := by
    have i1 : Integrable (fun ω => (⟪x 1 ω, w⟫_ℝ ^ 2 / R ^ 2 + R ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2) / 2) μ :=
      (((int_sq hA w).div_const _).add ((int_sq hA v).const_mul _)).div_const 2
    calc _ ≤ ∫ ω, (⟪x 1 ω, w⟫_ℝ ^ 2 / R ^ 2 + R ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2) / 2 ∂μ :=
          integral_mono (hA.integrable_cov w v) i1 hpt
      _ = _ := by
          rw [integral_div, integral_add ((int_sq hA w).div_const _) ((int_sq hA v).const_mul _),
            integral_div, integral_const_mul, ← q_eq hA, ← q_eq hA]
  have hq := q_le_norm hA w
  have : ⟪w, H w⟫_ℝ / R ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [div_le_iff₀ hR2]; linarith
  linarith

/-- First-order condition: `E⟨ξ, v⟩ = 0`. -/
theorem resid_mean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (v : Hs d) :
    Integrable (fun ω => ⟪residual x z θstar 1 ω, v⟫_ℝ) μ ∧
    ∫ ω, ⟪residual x z θstar 1 ω, v⟫_ℝ ∂μ = 0 := by
  have hz : Integrable (z 1) μ := hA.memLp_z.integrable (by norm_num)
  have hzv : Integrable (fun ω => ⟪v, z 1 ω⟫_ℝ) μ := hz.const_inner v
  have hxv : Integrable (fun ω => ⟪x 1 ω, θstar⟫_ℝ * ⟪x 1 ω, v⟫_ℝ) μ := hA.integrable_cov θstar v
  have e : (fun ω => ⟪residual x z θstar 1 ω, v⟫_ℝ) =
      fun ω => ⟪v, z 1 ω⟫_ℝ - ⟪x 1 ω, θstar⟫_ℝ * ⟪x 1 ω, v⟫_ℝ := by
    funext ω
    simp only [AvgLMS.Expect.residual, inner_sub_left, real_inner_smul_left,
      real_inner_comm (x 1 ω) θstar, real_inner_comm v (z 1 ω)]
  rw [e]
  refine ⟨hzv.sub hxv, ?_⟩
  rw [integral_sub hzv hxv, ← hA.cov_eq θstar v, integral_inner hz v]
  -- objective formula
  have hf : ∀ θ : Hs d, lsObjective μ x z θ = (1 / 2) * ⟪θ, H θ⟫_ℝ - ⟪θ, ∫ ω, z 1 ω ∂μ⟫_ℝ := by
    intro θ
    have h1 : Integrable (fun ω => ⟪θ, x 1 ω⟫_ℝ ^ 2) μ := by
      refine (hA.integrable_cov θ θ).congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [real_inner_comm θ (x 1 ω)]; ring
    have h2 : Integrable (fun ω => 2 * ⟪θ, z 1 ω⟫_ℝ) μ := (hz.inner_const θ |>.congr
      (Filter.Eventually.of_forall fun ω => by simp [real_inner_comm])).const_mul 2
    unfold lsObjective
    rw [integral_sub h1 h2, integral_const_mul, ← integral_inner hz, hA.cov_eq θ θ]
    have : ∫ ω, ⟪θ, x 1 ω⟫_ℝ ^ 2 ∂μ = ∫ ω, ⟪x 1 ω, θ⟫_ℝ * ⟪x 1 ω, θ⟫_ℝ ∂μ := by
      congr 1; funext ω; rw [real_inner_comm θ (x 1 ω)]; ring
    rw [this]; ring
  set m := ∫ ω, z 1 ω ∂μ
  set L := ⟪θstar, H v⟫_ℝ - ⟪m, v⟫_ℝ with hL
  set Q := ⟪v, H v⟫_ℝ with hQ
  have hQ0 : 0 ≤ Q := q_nonneg hA v
  have key : ∀ t : ℝ, 0 ≤ t * L + t ^ 2 * Q / 2 := by
    intro t
    have h := hA.isMin (θstar + t • v)
    rw [hf, hf] at h
    have hs : ⟪v, H θstar⟫_ℝ = ⟪θstar, H v⟫_ℝ := by
      rw [real_inner_comm (H θstar) v, H_symm hA]
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at h
    rw [hs] at h
    have hc := real_inner_comm v m
    rw [hL, hQ, hc]
    linarith
  have hs : 0 < 1 / (Q + 1) := by positivity
  have hsQ : 1 / (Q + 1) * Q ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have h := key (-L * (1 / (Q + 1)))
  have hL2 : L ^ 2 * (1 / (Q + 1)) ≤ 0 := by nlinarith [sq_nonneg L, mul_nonneg (sq_nonneg L) hs.le]
  have : L ^ 2 ≤ 0 := by
    by_contra hc; have hc' : 0 < L ^ 2 := not_le.1 hc; nlinarith [mul_pos hc' hs]
  have hL0 : L = 0 := by nlinarith [sq_nonneg L]
  have := real_inner_comm v m
  linarith


/-! ### σ-algebras, measurability, independence -/

noncomputable def obsSig {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (j : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (x (j + 1) ω, z (j + 1) ω)) inferInstance

noncomputable def past {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ {j : ℕ | j < k}, obsSig x z j

theorem obs_le_past {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) {j k : ℕ} (h : j < k) :
    obsSig x z j ≤ past x z k :=
  le_iSup₂ (f := fun j (_ : j ∈ {j : ℕ | j < k}) => obsSig x z j) j h

theorem past_mono {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (k : ℕ) :
    past x z k ≤ past x z (k + 1) :=
  iSup₂_le fun j hj => obs_le_past x z (Nat.lt_succ_of_lt hj)

theorem pair_meas_past {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (k : ℕ) :
    Measurable[past x z (k + 1)] (fun ω => (x (k + 1) ω, z (k + 1) ω)) :=
  (comap_measurable (fun ω => (x (k + 1) ω, z (k + 1) ω))).mono
    (obs_le_past x z (Nat.lt_succ_self k)) le_rfl

theorem obs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (j : ℕ) :
    obsSig x z j ≤ ‹MeasurableSpace Ω› :=
  ((hA.measurable_x (j + 1)).prodMk (hA.measurable_z (j + 1))).comap_le

theorem past_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (k : ℕ) :
    past x z k ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun j _ => obs_le hA j

theorem etaR_meas_past {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d)
    (x z : ℕ → Ω → Hs d) (θstar : Hs d) :
    ∀ r n, Measurable[past x z n] (etaR γ H x (AvgLMS.Expect.residual x z θstar) r n)
  | 0, 0 => measurable_const
  | 0, n + 1 => by
    have h1 := (etaR_meas_past γ H x z θstar 0 n).mono (past_mono x z n) le_rfl
    have h2 : Measurable[past x z (n + 1)] (AvgLMS.Expect.residual x z θstar (n + 1)) :=
      (Continuous.measurable (by fun_prop :
        Continuous fun p : Hs d × Hs d => p.2 - ⟪θstar, p.1⟫_ℝ • p.1)).comp (pair_meas_past x z n)
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d => (1 - γ • H) p.1 + γ • p.2)).comp (h1.prodMk h2)
    exact h
  | r + 1, 0 => measurable_const
  | r + 1, n + 1 => by
    have h1 := (etaR_meas_past γ H x z θstar (r + 1) n).mono (past_mono x z n) le_rfl
    have h2 := (etaR_meas_past γ H x z θstar r n).mono (past_mono x z n) le_rfl
    have h3 : Measurable[past x z (n + 1)] (x (n + 1)) :=
      measurable_fst.comp (pair_meas_past x z n)
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d × Hs d =>
        (1 - γ • H) p.1 + γ • (H p.2.1 - ⟪p.2.2, p.2.1⟫_ℝ • p.2.2))).comp
      (h1.prodMk (h2.prodMk h3))
    exact h

theorem indep_past {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) {E : Type*} [MeasurableSpace E] (k : ℕ) (f : Ω → E)
    (hf : Measurable[past x z k] f) :
    IndepFun f (fun ω => (x (k + 1) ω, z (k + 1) ω)) μ := by
  have hind : iIndep (obsSig x z) μ := (iIndepFun_iff_iIndep _ _ μ).1 hA.indep
  have hI := indep_iSup_of_disjoint (obs_le hA) hind (S := {j : ℕ | j < k}) (T := {k})
    (Set.disjoint_singleton_right.2 (lt_irrefl k))
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI hf.comap_le) ?_
  exact le_iSup₂ (f := fun j (_ : j ∈ ({k} : Set ℕ)) => obsSig x z j) k rfl

theorem lint_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) {E : Type*} [MeasurableSpace E] (k : ℕ) (f : Ω → E)
    (hfp : Measurable[past x z k] f) (hf : Measurable f)
    (Φ : E × (Hs d × Hs d) → ENNReal) (hΦ : Measurable Φ) (G : E → ENNReal) (hG : Measurable G)
    (hle : ∀ p, ∫⁻ ω, Φ (p, (x 1 ω, z 1 ω)) ∂μ ≤ G p) :
    ∫⁻ ω, Φ (f ω, (x (k + 1) ω, z (k + 1) ω)) ∂μ ≤ ∫⁻ ω, G (f ω) ∂μ := by
  have hym : Measurable fun ω => (x (k + 1) ω, z (k + 1) ω) :=
    (hA.measurable_x _).prodMk (hA.measurable_z _)
  have hy1 : Measurable fun ω => (x 1 ω, z 1 ω) := (hA.measurable_x _).prodMk (hA.measurable_z _)
  have hmap : μ.map (fun ω => (x (k + 1) ω, z (k + 1) ω)) = μ.map (fun ω => (x 1 ω, z 1 ω)) :=
    (hA.identDistrib k).map_eq
  have hI := indep_past hA k f hfp
  calc ∫⁻ ω, Φ (f ω, (x (k + 1) ω, z (k + 1) ω)) ∂μ
      = ∫⁻ p, Φ p ∂(μ.map fun ω => (f ω, (x (k + 1) ω, z (k + 1) ω))) :=
        (lintegral_map hΦ (hf.prodMk hym)).symm
    _ = ∫⁻ p, ∫⁻ y, Φ (p, y) ∂(μ.map fun ω => (x 1 ω, z 1 ω)) ∂(μ.map f) := by
        rw [hI.map_prod_eq_prod_map_map hf.aemeasurable hym.aemeasurable,
          lintegral_prod _ hΦ.aemeasurable, hmap]
    _ ≤ ∫⁻ p, G p ∂(μ.map f) := by
        refine lintegral_mono fun p => ?_
        dsimp only
        have hm : Measurable fun y : Hs d × Hs d => Φ (p, y) :=
          hΦ.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_map hm hy1]
        exact hle p
    _ = ∫⁻ ω, G (f ω) ∂μ := lintegral_map hG hf

/-! ### the contraction `I - γH` -/

theorem A_apply {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (v : Hs d) :
    (1 - γ • H) v = v - γ • H v := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply]

theorem A_symm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (a v : Hs d) :
    ⟪(1 - γ • H) a, v⟫_ℝ = ⟪a, (1 - γ • H) v⟫_ℝ := by
  rw [A_apply, A_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, H_symm hA]

theorem contr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (v : Hs d) :
    ‖(1 - γ • H) v‖ ^ 2 + γ * ⟪v, H v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  rw [A_apply, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  have h1 := normH_le hA v
  have hq := q_nonneg hA v
  have : γ ^ 2 * ‖H v‖ ^ 2 ≤ γ * ⟪v, H v⟫_ℝ := by
    calc γ ^ 2 * ‖H v‖ ^ 2 ≤ γ ^ 2 * (R ^ 2 * ⟪v, H v⟫_ℝ) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg γ)
      _ = γ * (γ * R ^ 2) * ⟪v, H v⟫_ℝ := by ring
      _ ≤ γ * 1 * ⟪v, H v⟫_ℝ := by gcongr
      _ = γ * ⟪v, H v⟫_ℝ := by ring
  linarith

theorem inner_sq_le {d : ℕ} (a b : Hs d) : ⟪a, b⟫_ℝ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have := abs_real_inner_le_norm a b
  have h0 := abs_nonneg ⟪a, b⟫_ℝ
  rw [← sq_abs, ← mul_pow]
  exact pow_le_pow_left₀ h0 this 2

/-! ### pointwise second moments -/

theorem step0_pt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ α : ℝ) (v : Hs d) :
    Integrable (fun ω => (α + γ * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ) ^ 2) μ ∧
    ∫ ω, (α + γ * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ) ^ 2 ∂μ ≤
      α ^ 2 + γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ) := by
  obtain ⟨i1, h1⟩ := resid_mean hA v
  have i2 := hA.integrable_noise v
  have e : (fun ω => (α + γ * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ) ^ 2) =
      fun ω => α ^ 2 + ((2 * α * γ) * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ +
        γ ^ 2 * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ ^ 2) := by
    funext ω; ring
  have i3 : Integrable (fun ω => (2 * α * γ) * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ +
      γ ^ 2 * ⟪AvgLMS.Expect.residual x z θstar 1 ω, v⟫_ℝ ^ 2) μ :=
    (i1.const_mul (2 * α * γ)).add (i2.const_mul (γ ^ 2))
  rw [e]
  refine ⟨(integrable_const _).add i3, ?_⟩
  rw [integral_add (integrable_const _) i3, integral_add (i1.const_mul _) (i2.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, h1]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, zero_add]
  have := mul_le_mul_of_nonneg_left (hA.noise_le v) (sq_nonneg γ)
  linarith

theorem iP2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (b v : Hs d) :
    Integrable (fun ω => ⟪x 1 ω, b⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2) μ := by
  refine ((hA.integrable_fourth v).const_mul (‖b‖ ^ 2)).mono' ?_ ?_
  · exact ((((hA.measurable_x 1).inner measurable_const).pow_const 2).mul
      (((hA.measurable_x 1).inner measurable_const).pow_const 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hb := inner_sq_le (x 1 ω) b
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ⟪x 1 ω, b⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 ≤ (‖x 1 ω‖ ^ 2 * ‖b‖ ^ 2) * ⟪x 1 ω, v⟫_ℝ ^ 2 :=
          mul_le_mul_of_nonneg_right hb (sq_nonneg _)
      _ = ‖b‖ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2) := by ring

theorem stepS_pt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ α β : ℝ) (b v : Hs d) (hβ : β = ⟪b, H v⟫_ℝ) :
    Integrable (fun ω => (α + γ * (β - ⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, v⟫_ℝ)) ^ 2) μ ∧
    ∫ ω, (α + γ * (β - ⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, v⟫_ℝ)) ^ 2 ∂μ ≤
      α ^ 2 + γ ^ 2 * ∫ ω, ⟪x 1 ω, b⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 ∂μ := by
  have iP := hA.integrable_cov b v
  have i2 := iP2 hA b v
  have e : (fun ω => (α + γ * (β - ⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, v⟫_ℝ)) ^ 2) = fun ω =>
      (α + γ * β) ^ 2 + ((-2 * (α + γ * β) * γ) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, v⟫_ℝ) +
        γ ^ 2 * (⟪x 1 ω, b⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2)) := by
    funext ω; ring
  have i3 : Integrable (fun ω => (-2 * (α + γ * β) * γ) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, v⟫_ℝ) +
      γ ^ 2 * (⟪x 1 ω, b⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2)) μ :=
    (iP.const_mul (-2 * (α + γ * β) * γ)).add (i2.const_mul (γ ^ 2))
  rw [e]
  refine ⟨(integrable_const _).add i3, ?_⟩
  rw [integral_add (integrable_const _) i3, integral_add (iP.const_mul _) (i2.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, ← hA.cov_eq b v, ← hβ]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  nlinarith [sq_nonneg (γ * β)]

/-! ### Tonelli bound -/

theorem swap_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (f : Ω → Hs d) (hf : Measurable f) (c : ℝ)
    (hc : 0 ≤ c)
    (hcov : ∀ w : Hs d, ∫⁻ ω, ENNReal.ofReal (⟪f ω, w⟫_ℝ ^ 2) ∂μ ≤ ENNReal.ofReal (c * ‖w‖ ^ 2))
    (W : Hs d → ℝ) (hW : Measurable W) (hW0 : ∀ y, 0 ≤ W y)
    (hWi : Integrable (fun ω => ‖x 1 ω‖ ^ 2 * W (x 1 ω)) μ) :
    ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (⟪x 1 ω', f ω⟫_ℝ ^ 2 * W (x 1 ω')) ∂μ ∂μ ≤
      ENNReal.ofReal (c * ∫ ω, ‖x 1 ω‖ ^ 2 * W (x 1 ω) ∂μ) := by
  have hx := hA.measurable_x 1
  have hF : Measurable (Function.uncurry fun ω ω' =>
      ENNReal.ofReal (⟪x 1 ω', f ω⟫_ℝ ^ 2 * W (x 1 ω'))) :=
    ((((hx.comp measurable_snd).inner (hf.comp measurable_fst)).pow_const 2).mul
      (hW.comp (hx.comp measurable_snd))).ennreal_ofReal
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc ∫⁻ ω', ∫⁻ ω, ENNReal.ofReal (⟪x 1 ω', f ω⟫_ℝ ^ 2 * W (x 1 ω')) ∂μ ∂μ
      ≤ ∫⁻ ω', ENNReal.ofReal (c * (‖x 1 ω'‖ ^ 2 * W (x 1 ω'))) ∂μ := by
        refine lintegral_mono fun ω' => ?_
        have e : (fun ω => ENNReal.ofReal (⟪x 1 ω', f ω⟫_ℝ ^ 2 * W (x 1 ω'))) =
            fun ω => ENNReal.ofReal (⟪f ω, x 1 ω'⟫_ℝ ^ 2) * ENNReal.ofReal (W (x 1 ω')) := by
          funext ω; rw [real_inner_comm, ENNReal.ofReal_mul (sq_nonneg _)]
        rw [e, lintegral_mul_const _ ((hf.inner measurable_const).pow_const 2).ennreal_ofReal]
        calc _ ≤ ENNReal.ofReal (c * ‖x 1 ω'‖ ^ 2) * ENNReal.ofReal (W (x 1 ω')) := by
              gcongr; exact hcov _
          _ = _ := by
              rw [← ENNReal.ofReal_mul (mul_nonneg hc (sq_nonneg _))]; congr 1; ring
    _ = ENNReal.ofReal (∫ ω', c * (‖x 1 ω'‖ ^ 2 * W (x 1 ω')) ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hWi.const_mul c)
          (Filter.Eventually.of_forall fun ω' => mul_nonneg hc
            (mul_nonneg (sq_nonneg _) (hW0 _)))]
    _ = _ := by rw [integral_const_mul]

/-! ### Part A: the covariance bound (Eq. 17) -/

theorem cov_step0 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (n : ℕ)
    (ih : ∀ w : Hs d, ∫⁻ ω, ENNReal.ofReal
      (⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) 0 n ω, w⟫_ℝ ^ 2) ∂μ ≤
        ENNReal.ofReal (γ * σ ^ 2 * ‖w‖ ^ 2))
    (v : Hs d) :
    ∫⁻ ω, ENNReal.ofReal
      (⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) 0 (n + 1) ω, v⟫_ℝ ^ 2) ∂μ ≤
        ENNReal.ofReal (γ * σ ^ 2 * ‖v‖ ^ 2) := by
  set ξ := AvgLMS.Expect.residual x z θstar with hξ
  set e := etaR γ H x ξ 0 n with he
  set Av := (1 - γ • H) v with hAv
  let Φ : Hs d × (Hs d × Hs d) → ENNReal := fun q =>
    ENNReal.ofReal ((⟪q.1, Av⟫_ℝ + γ * ⟪q.2.2 - ⟪θstar, q.2.1⟫_ℝ • q.2.1, v⟫_ℝ) ^ 2)
  have hΦ : Measurable Φ := ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  let G : Hs d → ENNReal := fun a =>
    ENNReal.ofReal (⟪a, Av⟫_ℝ ^ 2) + ENNReal.ofReal (γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ))
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))).add measurable_const
  have hem : Measurable e := (etaR_meas_past γ H x z θstar 0 n).mono (past_le hA n) le_rfl
  have hpt : ∀ a : Hs d, ∫⁻ ω, Φ (a, (x 1 ω, z 1 ω)) ∂μ ≤ G a := by
    intro a
    obtain ⟨hi, hle⟩ := step0_pt hA γ ⟪a, Av⟫_ℝ v
    calc ∫⁻ ω, Φ (a, (x 1 ω, z 1 ω)) ∂μ
          = ENNReal.ofReal (∫ ω, (⟪a, Av⟫_ℝ + γ * ⟪ξ 1 ω, v⟫_ℝ) ^ 2 ∂μ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hi
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
          rfl
      _ ≤ ENNReal.ofReal (⟪a, Av⟫_ℝ ^ 2 + γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ)) :=
          ENNReal.ofReal_le_ofReal hle
      _ ≤ G a := ENNReal.ofReal_add_le
  have hstep : ∀ ω, ⟪etaR γ H x ξ 0 (n + 1) ω, v⟫_ℝ =
      ⟪e ω, Av⟫_ℝ + γ * ⟪z (n + 1) ω - ⟪θstar, x (n + 1) ω⟫_ℝ • x (n + 1) ω, v⟫_ℝ := by
    intro ω
    show ⟪(1 - γ • H) (e ω) + γ • ξ (n + 1) ω, v⟫_ℝ = _
    rw [inner_add_left, real_inner_smul_left, A_symm hA]
    rfl
  have hq := q_nonneg hA v
  calc ∫⁻ ω, ENNReal.ofReal (⟪etaR γ H x ξ 0 (n + 1) ω, v⟫_ℝ ^ 2) ∂μ
        = ∫⁻ ω, Φ (e ω, (x (n + 1) ω, z (n + 1) ω)) ∂μ := by
          refine lintegral_congr fun ω => ?_
          simp only [Φ]
          rw [hstep]
      _ ≤ ∫⁻ ω, G (e ω) ∂μ :=
          lint_indep hA n e (etaR_meas_past γ H x z θstar 0 n) hem Φ hΦ G hG hpt
      _ = ∫⁻ ω, ENNReal.ofReal (⟪e ω, Av⟫_ℝ ^ 2) ∂μ +
          ENNReal.ofReal (γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (γ * σ ^ 2 * ‖Av‖ ^ 2) +
          ENNReal.ofReal (γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ)) := by
          gcongr; exact ih Av
      _ = ENNReal.ofReal (γ * σ ^ 2 * ‖Av‖ ^ 2 + γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ)) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (γ * σ ^ 2 * ‖v‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have := contr hA γ hγ0 hγR v
          have hs : 0 ≤ γ * σ ^ 2 := by positivity
          have e2 : γ * σ ^ 2 * ‖Av‖ ^ 2 + γ ^ 2 * (σ ^ 2 * ⟪v, H v⟫_ℝ) =
              γ * σ ^ 2 * (‖Av‖ ^ 2 + γ * ⟪v, H v⟫_ℝ) := by ring
          rw [e2]
          exact mul_le_mul_of_nonneg_left this hs

theorem cov_stepS {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (r n : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (ihr : ∀ w : Hs d, ∫⁻ ω, ENNReal.ofReal
      (⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r n ω, w⟫_ℝ ^ 2) ∂μ ≤
        ENNReal.ofReal (c * ‖w‖ ^ 2))
    (ih : ∀ w : Hs d, ∫⁻ ω, ENNReal.ofReal
      (⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) (r + 1) n ω, w⟫_ℝ ^ 2) ∂μ ≤
        ENNReal.ofReal (γ * R ^ 2 * c * ‖w‖ ^ 2))
    (v : Hs d) :
    ∫⁻ ω, ENNReal.ofReal
      (⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) (r + 1) (n + 1) ω, v⟫_ℝ ^ 2) ∂μ ≤
        ENNReal.ofReal (γ * R ^ 2 * c * ‖v‖ ^ 2) := by
  set ξ := AvgLMS.Expect.residual x z θstar with hξ
  set a := etaR γ H x ξ (r + 1) n with ha
  set b := etaR γ H x ξ r n with hb
  set Av := (1 - γ • H) v with hAv
  have ham : Measurable a := (etaR_meas_past γ H x z θstar (r + 1) n).mono (past_le hA n) le_rfl
  have hbm : Measurable b := (etaR_meas_past γ H x z θstar r n).mono (past_le hA n) le_rfl
  have hpp : Measurable[past x z n] (fun ω => (a ω, b ω)) :=
    (etaR_meas_past γ H x z θstar (r + 1) n).prodMk (etaR_meas_past γ H x z θstar r n)
  let Φ : (Hs d × Hs d) × (Hs d × Hs d) → ENNReal := fun q =>
    ENNReal.ofReal ((⟪q.1.1, Av⟫_ℝ + γ * (⟪q.1.2, H v⟫_ℝ - ⟪q.2.1, q.1.2⟫_ℝ * ⟪q.2.1, v⟫_ℝ)) ^ 2)
  have hΦ : Measurable Φ := ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  let K : (Hs d × Hs d) × Ω → ENNReal := fun q =>
    ENNReal.ofReal (⟪x 1 q.2, q.1.2⟫_ℝ ^ 2 * ⟪x 1 q.2, v⟫_ℝ ^ 2)
  have hK : Measurable K :=
    (((((hA.measurable_x 1).comp measurable_snd).inner
      (measurable_snd.comp measurable_fst)).pow_const 2).mul
      ((((hA.measurable_x 1).comp measurable_snd).inner measurable_const).pow_const 2)).ennreal_ofReal
  let G : Hs d × Hs d → ENNReal := fun p =>
    ENNReal.ofReal (⟪p.1, Av⟫_ℝ ^ 2) + ENNReal.ofReal (γ ^ 2) * ∫⁻ ω', K (p, ω') ∂μ
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))).add
      (measurable_const.mul hK.lintegral_prod_right')
  have hpt : ∀ p : Hs d × Hs d, ∫⁻ ω, Φ (p, (x 1 ω, z 1 ω)) ∂μ ≤ G p := by
    intro p
    obtain ⟨hi, hle⟩ := stepS_pt hA γ ⟪p.1, Av⟫_ℝ ⟪p.2, H v⟫_ℝ p.2 v rfl
    have hi2 := iP2 hA p.2 v
    calc ∫⁻ ω, Φ (p, (x 1 ω, z 1 ω)) ∂μ
          = ENNReal.ofReal (∫ ω, (⟪p.1, Av⟫_ℝ + γ * (⟪p.2, H v⟫_ℝ -
              ⟪x 1 ω, p.2⟫_ℝ * ⟪x 1 ω, v⟫_ℝ)) ^ 2 ∂μ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hi
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      _ ≤ ENNReal.ofReal (⟪p.1, Av⟫_ℝ ^ 2 +
            γ ^ 2 * ∫ ω, ⟪x 1 ω, p.2⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 ∂μ) :=
          ENNReal.ofReal_le_ofReal hle
      _ ≤ ENNReal.ofReal (⟪p.1, Av⟫_ℝ ^ 2) +
            ENNReal.ofReal (γ ^ 2 * ∫ ω, ⟪x 1 ω, p.2⟫_ℝ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 ∂μ) :=
          ENNReal.ofReal_add_le
      _ = G p := by
          simp only [G, K]
          rw [ENNReal.ofReal_mul (sq_nonneg _), ofReal_integral_eq_lintegral_ofReal hi2
            (Filter.Eventually.of_forall fun _ => by positivity)]
  have hstep : ∀ ω, ⟪etaR γ H x ξ (r + 1) (n + 1) ω, v⟫_ℝ =
      ⟪a ω, Av⟫_ℝ + γ * (⟪b ω, H v⟫_ℝ - ⟪x (n + 1) ω, b ω⟫_ℝ * ⟪x (n + 1) ω, v⟫_ℝ) := by
    intro ω
    show ⟪(1 - γ • H) (a ω) + γ • (H (b ω) - ⟪x (n + 1) ω, b ω⟫_ℝ • x (n + 1) ω), v⟫_ℝ = _
    rw [inner_add_left, real_inner_smul_left, A_symm hA, inner_sub_left, real_inner_smul_left,
      H_symm hA]
  have hc' : 0 ≤ γ * R ^ 2 * c := by positivity
  have hq := q_nonneg hA v
  have hmidm : Measurable fun ω => ∫⁻ ω', K ((a ω, b ω), ω') ∂μ :=
    hK.lintegral_prod_right'.comp (ham.prodMk hbm)
  calc ∫⁻ ω, ENNReal.ofReal (⟪etaR γ H x ξ (r + 1) (n + 1) ω, v⟫_ℝ ^ 2) ∂μ
        = ∫⁻ ω, Φ ((a ω, b ω), (x (n + 1) ω, z (n + 1) ω)) ∂μ := by
          refine lintegral_congr fun ω => ?_
          simp only [Φ]
          rw [hstep]
      _ ≤ ∫⁻ ω, G (a ω, b ω) ∂μ :=
          lint_indep hA n (fun ω => (a ω, b ω)) hpp (ham.prodMk hbm) Φ hΦ G hG hpt
      _ = ∫⁻ ω, ENNReal.ofReal (⟪a ω, Av⟫_ℝ ^ 2) ∂μ + ENNReal.ofReal (γ ^ 2) *
          ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (⟪x 1 ω', b ω⟫_ℝ ^ 2 * ⟪x 1 ω', v⟫_ℝ ^ 2) ∂μ ∂μ := by
          rw [lintegral_add_left ((ham.inner measurable_const).pow_const 2).ennreal_ofReal,
            lintegral_const_mul _ hmidm]
      _ ≤ ENNReal.ofReal (γ * R ^ 2 * c * ‖Av‖ ^ 2) + ENNReal.ofReal (γ ^ 2) *
          ENNReal.ofReal (c * ∫ ω, ‖x 1 ω‖ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 ∂μ) := by
          gcongr
          · exact ih Av
          · exact swap_bound hA b hbm c hc ihr (fun y => ⟪y, v⟫_ℝ ^ 2)
              ((measurable_id.inner measurable_const).pow_const 2) (fun y => sq_nonneg _)
              (hA.integrable_fourth v)
      _ ≤ ENNReal.ofReal (γ * R ^ 2 * c * ‖Av‖ ^ 2) +
          ENNReal.ofReal (γ ^ 2 * (c * (R ^ 2 * ⟪v, H v⟫_ℝ))) := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          gcongr
          exact hA.fourth_le v
      _ = ENNReal.ofReal (γ * R ^ 2 * c * ‖Av‖ ^ 2 + γ ^ 2 * (c * (R ^ 2 * ⟪v, H v⟫_ℝ))) :=
          (ENNReal.ofReal_add (mul_nonneg hc' (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) (mul_nonneg hc (mul_nonneg (sq_nonneg _) hq)))).symm
      _ ≤ ENNReal.ofReal (γ * R ^ 2 * c * ‖v‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have := contr hA γ hγ0 hγR v
          have e : γ * R ^ 2 * c * ‖Av‖ ^ 2 + γ ^ 2 * (c * (R ^ 2 * ⟪v, H v⟫_ℝ)) =
              γ * R ^ 2 * c * (‖Av‖ ^ 2 + γ * ⟪v, H v⟫_ℝ) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_left this hc'

theorem cov_lint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1) :
    ∀ r n (v : Hs d), ∫⁻ ω, ENNReal.ofReal
      (⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r n ω, v⟫_ℝ ^ 2) ∂μ ≤
        ENNReal.ofReal (γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 * ‖v‖ ^ 2) := by
  have hR := hA.R_pos
  intro r
  induction r with
  | zero =>
    intro n
    induction n with
    | zero => intro v; simp [etaR]
    | succ n ih =>
      intro v
      have e : ∀ w : Hs d, γ ^ (0 + 1) * R ^ (2 * 0) * σ ^ 2 * ‖w‖ ^ 2 = γ * σ ^ 2 * ‖w‖ ^ 2 :=
        fun w => by ring
      rw [e]
      exact cov_step0 hA γ hγ0 hγR n (fun w => by rw [← e]; exact ih w) v
  | succ r ihr =>
    intro n
    have hc : 0 ≤ γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 := by positivity
    have e : ∀ w : Hs d, γ ^ (r + 1 + 1) * R ^ (2 * (r + 1)) * σ ^ 2 * ‖w‖ ^ 2 =
        γ * R ^ 2 * (γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2) * ‖w‖ ^ 2 := fun w => by ring
    induction n with
    | zero => intro v; simp [etaR]
    | succ n ih =>
      intro v
      rw [e]
      exact cov_stepS hA γ hγ0 hγR r n _ hc (ihr n) (fun w => by rw [← e]; exact ih w) v

end AvgLMSRB

namespace AvgLMSRB

open AvgLMS.Expect

/-! ### Part B: `E q(ηʳₖ) ≤ γ^{r+1} R^{2r} σ² R²` -/

theorem qe_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (r k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω,
      H (etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω)⟫_ℝ ∂μ ≤
      ENNReal.ofReal (γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 * R ^ 2) := by
  set f := etaR γ H x (AvgLMS.Expect.residual x z θstar) r k with hf
  have hfm : Measurable f := (etaR_meas_past γ H x z θstar r k).mono (past_le hA k) le_rfl
  obtain ⟨i2, h2⟩ := norm_sq_x hA
  have hR := hA.R_pos
  have hc : 0 ≤ γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 := by positivity
  have e : ∀ ω, ENNReal.ofReal ⟪f ω, H (f ω)⟫_ℝ =
      ∫⁻ ω', ENNReal.ofReal (⟪x 1 ω', f ω⟫_ℝ ^ 2 * (fun _ : Hs d => (1 : ℝ)) (x 1 ω')) ∂μ := by
    intro ω
    rw [q_eq hA, ofReal_integral_eq_lintegral_ofReal (int_sq hA _)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    simp only [mul_one]
  calc ∫⁻ ω, ENNReal.ofReal ⟪f ω, H (f ω)⟫_ℝ ∂μ
        = ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (⟪x 1 ω', f ω⟫_ℝ ^ 2 *
            (fun _ : Hs d => (1 : ℝ)) (x 1 ω')) ∂μ ∂μ := lintegral_congr e
    _ ≤ ENNReal.ofReal (γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 *
          ∫ ω, ‖x 1 ω‖ ^ 2 * (fun _ : Hs d => (1 : ℝ)) (x 1 ω) ∂μ) :=
        swap_bound hA f hfm _ hc (cov_lint hA γ hγ0 hγR r k) (fun _ => 1) measurable_const
          (fun _ => zero_le_one) (by simpa using i2)
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        simp only [mul_one]
        exact mul_le_mul_of_nonneg_left h2 hc

/-! ### Part C: the remainder process -/

theorem etaR_sum_succ {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d)
    (x ξ : ℕ → Ω → Hs d) (n : ℕ) (ω : Ω) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), etaR γ H x ξ i (n + 1) ω =
      (∑ i ∈ Finset.range (r + 1), etaR γ H x ξ i n ω) -
        γ • H (∑ i ∈ Finset.range (r + 1), etaR γ H x ξ i n ω) + γ • ξ (n + 1) ω +
        γ • (H (∑ i ∈ Finset.range r, etaR γ H x ξ i n ω) -
          ⟪x (n + 1) ω, ∑ i ∈ Finset.range r, etaR γ H x ξ i n ω⟫_ℝ • x (n + 1) ω) := by
  induction r with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, map_zero,
      inner_zero_right, zero_smul, sub_zero, smul_zero, add_zero]
    rw [etaR]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i => etaR γ H x ξ i n ω) (r + 1),
      Finset.sum_range_succ (fun i => etaR γ H x ξ i n ω) r]
    rw [etaR]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, map_add, inner_add_right, add_smul, smul_add, smul_sub]
    abel

/-- The remainder `ηₖ − ∑_{i ≤ r} ηⁱₖ` of the order-`r` expansion (iterates started at `θ∗`). -/
noncomputable def rho {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (x z : ℕ → Ω → Hs d)
    (θstar : Hs d) (r k : ℕ) (ω : Ω) : Hs d :=
  (lmsIter γ θstar x z k ω - θstar) -
    ∑ i ∈ Finset.range (r + 1), etaR γ H x (AvgLMS.Expect.residual x z θstar) i k ω

theorem rho_zero {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (x z : ℕ → Ω → Hs d)
    (θstar : Hs d) (r : ℕ) (ω : Ω) : rho γ H x z θstar r 0 ω = 0 := by
  unfold rho
  rw [Finset.sum_eq_zero fun i _ => by cases i <;> rfl]
  simp [lmsIter]

theorem rho_succ {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (x z : ℕ → Ω → Hs d)
    (θstar : Hs d) (r n : ℕ) (ω : Ω) :
    rho γ H x z θstar r (n + 1) ω =
      rho γ H x z θstar r n ω - γ • (⟪x (n + 1) ω, rho γ H x z θstar r n ω⟫_ℝ • x (n + 1) ω) +
        γ • (H (etaR γ H x (AvgLMS.Expect.residual x z θstar) r n ω) -
          ⟪x (n + 1) ω, etaR γ H x (AvgLMS.Expect.residual x z θstar) r n ω⟫_ℝ • x (n + 1) ω) := by
  unfold rho
  rw [etaR_sum_succ, Finset.sum_range_succ (fun i => etaR γ H x _ i n ω) r]
  have hl : lmsIter γ θstar x z (n + 1) ω = lmsIter γ θstar x z n ω -
      γ • (⟪lmsIter γ θstar x z n ω, x (n + 1) ω⟫_ℝ • x (n + 1) ω - z (n + 1) ω) := rfl
  rw [hl]
  have hres : AvgLMS.Expect.residual x z θstar (n + 1) ω =
      z (n + 1) ω - ⟪θstar, x (n + 1) ω⟫_ℝ • x (n + 1) ω := rfl
  rw [hres]
  generalize (∑ i ∈ Finset.range r, etaR γ H x (AvgLMS.Expect.residual x z θstar) i n ω) = A
  generalize etaR γ H x (AvgLMS.Expect.residual x z θstar) r n ω = B
  generalize lmsIter γ θstar x z n ω = θ
  generalize x (n + 1) ω = X
  generalize z (n + 1) ω = Z
  simp only [map_add, inner_add_right, inner_sub_right, real_inner_comm θ X,
    real_inner_comm θstar X]
  module

theorem lms_meas_past {Ω : Type*} {d : ℕ} (γ : ℝ) (θ0 : Hs d) (x z : ℕ → Ω → Hs d) :
    ∀ k, Measurable[past x z k] (lmsIter γ θ0 x z k)
  | 0 => measurable_const
  | k + 1 => by
    have h1 := (lms_meas_past γ θ0 x z k).mono (past_mono x z k) le_rfl
    have h := (Continuous.measurable (by fun_prop :
      Continuous fun p : Hs d × Hs d × Hs d => p.1 - γ • (⟪p.1, p.2.1⟫_ℝ • p.2.1 - p.2.2))).comp
      (h1.prodMk (pair_meas_past x z k))
    exact h

theorem rho_meas_past {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (x z : ℕ → Ω → Hs d)
    (θstar : Hs d) (r k : ℕ) : Measurable[past x z k] (rho γ H x z θstar r k) := by
  have h1 := lms_meas_past γ θstar x z k
  have h2 : Measurable[past x z k] (fun ω => ∑ i ∈ Finset.range (r + 1),
      etaR γ H x (AvgLMS.Expect.residual x z θstar) i k ω) :=
    Finset.measurable_sum _ fun i _ => etaR_meas_past γ H x z θstar i k
  exact (h1.sub measurable_const).sub h2

/-- Pointwise (in the past) energy inequality for one step of the remainder recursion. -/
theorem energy_pt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (a b : Hs d) :
    ∫⁻ ω, ENNReal.ofReal (‖a - γ • (⟪x 1 ω, a⟫_ℝ • x 1 ω) + γ • (H b - ⟪x 1 ω, b⟫_ℝ • x 1 ω)‖ ^ 2
      + 2 * γ * (1 - γ * R ^ 2) * ⟪a, H a⟫_ℝ) ∂μ ≤
      ENNReal.ofReal (‖a‖ ^ 2 + 2 * γ ^ 2 * R ^ 2 * ⟪b, H b⟫_ℝ) := by
  set C := 2 * γ * (1 - γ * R ^ 2) with hC
  set c0 := ‖a‖ ^ 2 + 2 * γ * ⟪a, H b⟫_ℝ + 2 * γ ^ 2 * ‖H b‖ ^ 2 + C * ⟪a, H a⟫_ℝ with hc0
  have hpt : ∀ ω, ‖a - γ • (⟪x 1 ω, a⟫_ℝ • x 1 ω) + γ • (H b - ⟪x 1 ω, b⟫_ℝ • x 1 ω)‖ ^ 2
      + C * ⟪a, H a⟫_ℝ ≤
      c0 + (((((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) + (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) +
        (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
        2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) +
        2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2)) := by
    intro ω
    generalize x 1 ω = y
    have e1 : a - γ • (⟪y, a⟫_ℝ • y) + γ • (H b - ⟪y, b⟫_ℝ • y) =
        a + γ • ((H b - ⟪y, b⟫_ℝ • y) - ⟪y, a⟫_ℝ • y) := by module
    rw [e1, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 : ⟪a, (H b - ⟪y, b⟫_ℝ • y) - ⟪y, a⟫_ℝ • y⟫_ℝ =
        ⟪a, H b⟫_ℝ - ⟪y, b⟫_ℝ * ⟪y, a⟫_ℝ - ⟪y, a⟫_ℝ * ⟪y, a⟫_ℝ := by
      rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_comm y a]
    have h3 : ‖(H b - ⟪y, b⟫_ℝ • y) - ⟪y, a⟫_ℝ • y‖ ^ 2 ≤
        2 * ‖H b - ⟪y, b⟫_ℝ • y‖ ^ 2 + 2 * ‖⟪y, a⟫_ℝ • y‖ ^ 2 := by
      have h4 := norm_add_sq_real (H b - ⟪y, b⟫_ℝ • y) (⟪y, a⟫_ℝ • y)
      have h5 := norm_sub_sq_real (H b - ⟪y, b⟫_ℝ • y) (⟪y, a⟫_ℝ • y)
      nlinarith [sq_nonneg ‖(H b - ⟪y, b⟫_ℝ • y) + ⟪y, a⟫_ℝ • y‖]
    have h5 : ‖H b - ⟪y, b⟫_ℝ • y‖ ^ 2 =
        ‖H b‖ ^ 2 - 2 * (⟪y, b⟫_ℝ * ⟪y, H b⟫_ℝ) + ⟪y, b⟫_ℝ ^ 2 * ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_comm y (H b)]
    have h6 : ‖⟪y, a⟫_ℝ • y‖ ^ 2 = ⟪y, a⟫_ℝ ^ 2 * ‖y‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h7 := mul_le_mul_of_nonneg_left h3 (sq_nonneg γ)
    rw [h5, h6] at h7
    rw [h2, hc0]
    nlinarith [h7]
  have I1 : Integrable (fun ω => (-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ)) μ :=
    (hA.integrable_cov a b).const_mul _
  have I2 : Integrable (fun ω => (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) μ := (int_sq hA a).const_mul _
  have I3 : Integrable (fun ω => (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) μ :=
    (hA.integrable_cov b (H b)).const_mul _
  have I4 : Integrable (fun ω => 2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) μ :=
    (hA.integrable_fourth b).const_mul _
  have I5 : Integrable (fun ω => 2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2)) μ :=
    (hA.integrable_fourth a).const_mul _
  have I12 : Integrable (fun ω => (-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) μ := I1.add I2
  have I123 : Integrable (fun ω => ((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) μ :=
    I12.add I3
  have I1234 : Integrable (fun ω => (((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) μ := I123.add I4
  have I12345 : Integrable (fun ω => ((((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2)) μ := I1234.add I5
  have IU := (integrable_const c0).add I12345
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 1 - γ * R ^ 2 := by linarith
    positivity
  have hU0 : ∀ ω, 0 ≤ c0 + (((((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2)) := fun ω =>
    le_trans (add_nonneg (sq_nonneg _) (mul_nonneg hC0 (q_nonneg hA a))) (hpt ω)
  have hint : ∫ ω, (c0 + (((((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2))) ∂μ ≤
      ‖a‖ ^ 2 + 2 * γ ^ 2 * R ^ 2 * ⟪b, H b⟫_ℝ := by
    rw [integral_add (integrable_const c0) I12345, integral_add I1234 I5, integral_add I123 I4,
      integral_add I12 I3, integral_add I1 I2, integral_const, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      ← hA.cov_eq a b, ← q_eq hA a, ← hA.cov_eq b (H b)]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have hHH : ⟪b, H (H b)⟫_ℝ = ‖H b‖ ^ 2 := by
      rw [← H_symm hA, real_inner_self_eq_norm_sq]
    rw [hHH, hc0, hC]
    have f1 := mul_le_mul_of_nonneg_left (hA.fourth_le a) (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2)
    have f2 := mul_le_mul_of_nonneg_left (hA.fourth_le b) (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2)
    have hHb := sq_nonneg ‖H b‖
    nlinarith [f1, f2, sq_nonneg γ, hHb]
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (c0 + (((((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2))) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, (c0 + (((((-2 * γ) * (⟪x 1 ω, a⟫_ℝ * ⟪x 1 ω, b⟫_ℝ) +
      (-2 * γ) * ⟪x 1 ω, a⟫_ℝ ^ 2) + (-4 * γ ^ 2) * (⟪x 1 ω, b⟫_ℝ * ⟪x 1 ω, H b⟫_ℝ)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, b⟫_ℝ ^ 2)) +
      2 * γ ^ 2 * (‖x 1 ω‖ ^ 2 * ⟪x 1 ω, a⟫_ℝ ^ 2))) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal IU (Filter.Eventually.of_forall hU0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hint

theorem energy_step {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (r k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖rho γ H x z θstar r (k + 1) ω‖ ^ 2) ∂μ +
      ENNReal.ofReal (2 * γ * (1 - γ * R ^ 2)) *
        ∫⁻ ω, ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (‖rho γ H x z θstar r k ω‖ ^ 2) ∂μ +
      ENNReal.ofReal (2 * γ ^ 2 * R ^ 2) *
        ∫⁻ ω, ENNReal.ofReal ⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω,
          H (etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω)⟫_ℝ ∂μ := by
  set ρ := rho γ H x z θstar r k with hρ
  set e := etaR γ H x (AvgLMS.Expect.residual x z θstar) r k with he
  have hρm : Measurable ρ := (rho_meas_past γ H x z θstar r k).mono (past_le hA k) le_rfl
  have hem : Measurable e := (etaR_meas_past γ H x z θstar r k).mono (past_le hA k) le_rfl
  have hpp : Measurable[past x z k] (fun ω => (ρ ω, e ω)) :=
    (rho_meas_past γ H x z θstar r k).prodMk (etaR_meas_past γ H x z θstar r k)
  have hC0 : 0 ≤ 2 * γ * (1 - γ * R ^ 2) := by
    have : 0 ≤ 1 - γ * R ^ 2 := by linarith
    positivity
  have hβ0 : 0 ≤ 2 * γ ^ 2 * R ^ 2 := by positivity
  let Φ : (Hs d × Hs d) × (Hs d × Hs d) → ENNReal := fun q =>
    ENNReal.ofReal (‖q.1.1 - γ • (⟪q.2.1, q.1.1⟫_ℝ • q.2.1) + γ • (H q.1.2 - ⟪q.2.1, q.1.2⟫_ℝ • q.2.1)‖ ^ 2
      + 2 * γ * (1 - γ * R ^ 2) * ⟪q.1.1, H q.1.1⟫_ℝ)
  have hΦ : Measurable Φ := ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
  let G : Hs d × Hs d → ENNReal := fun p =>
    ENNReal.ofReal (‖p.1‖ ^ 2) + ENNReal.ofReal (2 * γ ^ 2 * R ^ 2) * ENNReal.ofReal ⟪p.2, H p.2⟫_ℝ
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))).add
      (measurable_const.mul (ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))))
  have hpt : ∀ p : Hs d × Hs d, ∫⁻ ω, Φ (p, (x 1 ω, z 1 ω)) ∂μ ≤ G p := by
    intro p
    calc ∫⁻ ω, Φ (p, (x 1 ω, z 1 ω)) ∂μ ≤
          ENNReal.ofReal (‖p.1‖ ^ 2 + 2 * γ ^ 2 * R ^ 2 * ⟪p.2, H p.2⟫_ℝ) :=
          energy_pt hA γ hγ0 hγR p.1 p.2
      _ ≤ G p := by
          refine le_trans ENNReal.ofReal_add_le ?_
          simp only [G]
          rw [ENNReal.ofReal_mul hβ0]
  have hm1 : Measurable fun ω => ENNReal.ofReal (‖rho γ H x z θstar r (k + 1) ω‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp
      (((rho_meas_past γ H x z θstar r (k + 1)).mono (past_le hA (k + 1)) le_rfl).norm.pow_const 2)
  have hm2 : Measurable fun ω => ENNReal.ofReal ⟪ρ ω, H (ρ ω)⟫_ℝ :=
    ENNReal.measurable_ofReal.comp (hρm.inner (H.continuous.measurable.comp hρm))
  have hm3 : Measurable fun ω => ENNReal.ofReal ⟪e ω, H (e ω)⟫_ℝ :=
    ENNReal.measurable_ofReal.comp (hem.inner (H.continuous.measurable.comp hem))
  calc _ = ∫⁻ ω, Φ ((ρ ω, e ω), (x (k + 1) ω, z (k + 1) ω)) ∂μ := by
        rw [← lintegral_const_mul _ hm2, ← lintegral_add_left hm1]
        refine lintegral_congr fun ω => ?_
        simp only [Φ]
        rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hC0 (q_nonneg hA _)),
          ENNReal.ofReal_mul hC0, rho_succ]
    _ ≤ ∫⁻ ω, G (ρ ω, e ω) ∂μ :=
        lint_indep hA k (fun ω => (ρ ω, e ω)) hpp (hρm.prodMk hem) Φ hΦ G hG hpt
    _ = _ := by
        simp only [G]
        rw [lintegral_add_left ((hρm.norm.pow_const 2).ennreal_ofReal), lintegral_const_mul _ hm3]

theorem tele {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (r : ℕ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖rho γ H x z θstar r n ω‖ ^ 2) ∂μ +
      ENNReal.ofReal (2 * γ * (1 - γ * R ^ 2)) * ∑ k ∈ Finset.range n,
        ∫⁻ ω, ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ ≤
      ENNReal.ofReal (2 * γ ^ 2 * R ^ 2) * ∑ k ∈ Finset.range n,
        ∫⁻ ω, ENNReal.ofReal ⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω,
          H (etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω)⟫_ℝ ∂μ := by
  induction n with
  | zero => simp [rho_zero]
  | succ n ih =>
    set L : ℕ → ENNReal := fun k => ∫⁻ ω, ENNReal.ofReal (‖rho γ H x z θstar r k ω‖ ^ 2) ∂μ
    set Q : ℕ → ENNReal := fun k =>
      ∫⁻ ω, ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ
    set E : ℕ → ENNReal := fun k =>
      ∫⁻ ω, ENNReal.ofReal ⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω,
        H (etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω)⟫_ℝ ∂μ
    set α := ENNReal.ofReal (2 * γ * (1 - γ * R ^ 2))
    set β := ENNReal.ofReal (2 * γ ^ 2 * R ^ 2)
    have hs : L (n + 1) + α * Q n ≤ L n + β * E n := energy_step hA γ hγ0 hγR r n
    have ih' : L n + α * ∑ k ∈ Finset.range n, Q k ≤ β * ∑ k ∈ Finset.range n, E k := ih
    show L (n + 1) + α * ∑ k ∈ Finset.range (n + 1), Q k ≤ β * ∑ k ∈ Finset.range (n + 1), E k
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
    calc L (n + 1) + (α * ∑ k ∈ Finset.range n, Q k + α * Q n)
        = (L (n + 1) + α * Q n) + α * ∑ k ∈ Finset.range n, Q k := by ring
      _ ≤ (L n + β * E n) + α * ∑ k ∈ Finset.range n, Q k := by gcongr
      _ = (L n + α * ∑ k ∈ Finset.range n, Q k) + β * E n := by ring
      _ ≤ β * ∑ k ∈ Finset.range n, E k + β * E n := by gcongr

theorem q_smul {d : ℕ} (H : Hs d →L[ℝ] Hs d) (c : ℝ) (v : Hs d) :
    ⟪c • v, H (c • v)⟫_ℝ = c ^ 2 * ⟪v, H v⟫_ℝ := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring

theorem q_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) {ι : Type*} (s : Finset ι) (w : ι → Hs d) :
    ⟪∑ i ∈ s, w i, H (∑ i ∈ s, w i)⟫_ℝ ≤ s.card * ∑ i ∈ s, ⟪w i, H (w i)⟫_ℝ := by
  rw [q_eq hA, Finset.sum_congr rfl fun i _ => q_eq hA (w i),
    ← integral_finsetSum s (fun i _ => int_sq hA (w i)), ← integral_const_mul]
  refine integral_mono (int_sq hA _)
    ((integrable_finsetSum s fun i _ => int_sq hA (w i)).const_mul _) fun ω => ?_
  simp only [inner_sum]
  exact sq_sum_le_card_mul_sum_sq

theorem avg_rho {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (x z : ℕ → Ω → Hs d)
    (θstar : Hs d) (r m : ℕ) (ω : Ω) :
    (avg (lmsIter γ θstar x z) m ω - θstar) -
        ∑ i ∈ Finset.range (r + 1), avg (etaR γ H x (AvgLMS.Expect.residual x z θstar) i) m ω =
      avg (rho γ H x z θstar r) m ω := by
  have hc : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hθ : θstar = ((m : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (m + 1), θstar := by
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hc, one_smul]
  unfold avg rho
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, smul_sub, smul_sub, ← hθ, Finset.sum_comm,
    Finset.smul_sum (s := Finset.range (r + 1))]

theorem final {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {x z : ℕ → Ω → Hs d} {H : Hs d →L[ℝ] Hs d} {θstar : Hs d} {R σ : ℝ}
    (hA : LMSAssumptions μ x z H θstar R σ) (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 < 1)
    (r m : ℕ) :
    Integrable (fun ω => ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ ∂μ ≤
      1 / (1 - γ * R ^ 2) * γ ^ (r + 2) * σ ^ 2 * R ^ (2 * r + 4) := by
  have hγR' : γ * R ^ 2 ≤ 1 := hγR.le
  have hR := hA.R_pos
  have hσ := hA.σ_pos
  have h1 : 0 < 1 - γ * R ^ 2 := by linarith
  have hCpos : 0 < 2 * γ * (1 - γ * R ^ 2) := by positivity
  have hβ0 : 0 ≤ 2 * γ ^ 2 * R ^ 2 := by positivity
  set cr := γ ^ (r + 1) * R ^ (2 * r) * σ ^ 2 * R ^ 2 with hcr
  have hcr0 : 0 ≤ cr := by positivity
  have hmρ : ∀ k, Measurable (rho γ H x z θstar r k) := fun k =>
    (rho_meas_past γ H x z θstar r k).mono (past_le hA k) le_rfl
  have ham : Measurable (avg (rho γ H x z θstar r) m) := by
    unfold avg
    exact (Finset.measurable_sum _ fun k _ => hmρ k).const_smul (((m : ℝ) + 1)⁻¹)
  have hgm : Measurable fun ω =>
      ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ :=
    ham.inner (H.continuous.measurable.comp ham)
  have hg0 : ∀ ω, 0 ≤ ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ :=
    fun ω => q_nonneg hA _
  have hc : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hgle : ∀ ω, ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ ≤
      ((m : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (m + 1),
        ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ := by
    intro ω
    unfold avg
    rw [q_smul]
    have h := q_sum_le hA (Finset.range (m + 1)) (fun k => rho γ H x z θstar r k ω)
    rw [Finset.card_range] at h
    push_cast at h
    calc ((m : ℝ) + 1)⁻¹ ^ 2 * ⟪∑ k ∈ Finset.range (m + 1), rho γ H x z θstar r k ω,
          H (∑ k ∈ Finset.range (m + 1), rho γ H x z θstar r k ω)⟫_ℝ
        ≤ ((m : ℝ) + 1)⁻¹ ^ 2 * (((m : ℝ) + 1) * ∑ k ∈ Finset.range (m + 1),
          ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ) := by gcongr
      _ = _ := by field_simp
  have hS : ∑ k ∈ Finset.range (m + 1),
      ∫⁻ ω, ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ ≤
      ENNReal.ofReal (2 * γ ^ 2 * R ^ 2 * (((m : ℝ) + 1) * cr) / (2 * γ * (1 - γ * R ^ 2))) := by
    rw [ENNReal.ofReal_div_of_pos hCpos, ENNReal.le_div_iff_mul_le
      (Or.inl (by simp [hCpos])) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    have hT := tele hA γ hγ0 hγR' r (m + 1)
    have hE : ∑ k ∈ Finset.range (m + 1),
        ∫⁻ ω, ENNReal.ofReal ⟪etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω,
          H (etaR γ H x (AvgLMS.Expect.residual x z θstar) r k ω)⟫_ℝ ∂μ ≤
        ENNReal.ofReal (((m : ℝ) + 1) * cr) := by
      calc _ ≤ ∑ k ∈ Finset.range (m + 1), ENNReal.ofReal cr :=
            Finset.sum_le_sum fun k _ => qe_bound hA γ hγ0 hγR' r k
        _ = ENNReal.ofReal (∑ k ∈ Finset.range (m + 1), cr) :=
            (ENNReal.ofReal_sum_of_nonneg fun k _ => hcr0).symm
        _ = _ := by simp
    calc ENNReal.ofReal (2 * γ * (1 - γ * R ^ 2)) * ∑ k ∈ Finset.range (m + 1),
          ∫⁻ ω, ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ
        ≤ _ := le_trans le_add_self hT
      _ ≤ ENNReal.ofReal (2 * γ ^ 2 * R ^ 2) * ENNReal.ofReal (((m : ℝ) + 1) * cr) := by gcongr
      _ = _ := (ENNReal.ofReal_mul hβ0).symm
  have hlin : ∫⁻ ω, ENNReal.ofReal
      ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ ∂μ ≤
      ENNReal.ofReal (1 / (1 - γ * R ^ 2) * γ ^ (r + 2) * σ ^ 2 * R ^ (2 * r + 4)) := by
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal ((m : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (m + 1),
          ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => q_nonneg hA _),
            ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
          exact ENNReal.ofReal_le_ofReal (hgle ω)
      _ = ENNReal.ofReal ((m : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (m + 1),
          ∫⁻ ω, ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ ∂μ := by
          have hqm : ∀ k, Measurable fun ω =>
              ENNReal.ofReal ⟪rho γ H x z θstar r k ω, H (rho γ H x z θstar r k ω)⟫_ℝ := fun k =>
            ENNReal.measurable_ofReal.comp ((hmρ k).inner (H.continuous.measurable.comp (hmρ k)))
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_finsetSum _ fun k _ => hqm k]
      _ ≤ ENNReal.ofReal ((m : ℝ) + 1)⁻¹ * ENNReal.ofReal
          (2 * γ ^ 2 * R ^ 2 * (((m : ℝ) + 1) * cr) / (2 * γ * (1 - γ * R ^ 2))) := by gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
          congr 1
          rw [hcr]
          field_simp
          ring
  have hfin : ∫⁻ ω, ENNReal.ofReal
      ⟪avg (rho γ H x z θstar r) m ω, H (avg (rho γ H x z θstar r) m ω)⟫_ℝ ∂μ < ⊤ :=
    lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨⟨hgm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
    hgm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

end AvgLMSRB

open MeasureTheory ProbabilityTheory InnerProductSpace RealInnerProductSpace AvgLMS.Expect in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ)
    (γ : ℝ) (hγ0 : 0 < γ) (hγR : γ * R ^ 2 < 1) (r n : ℕ) (hn : 1 ≤ n) :
    let rem : Ω → Hs d := fun ω =>
      (avg (lmsIter γ θstar x z) (n - 1) ω - θstar) -
        ∑ i ∈ Finset.range (r + 1), avg (etaR γ H x (residual x z θstar) i) (n - 1) ω
    Integrable (fun ω => ⟪rem ω, H (rem ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪rem ω, H (rem ω)⟫_ℝ ∂μ ≤
      1 / (1 - γ * R ^ 2) * γ ^ (r + 2) * σ ^ 2 * R ^ (2 * r + 4) := by
  intro rem
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hrem : ∀ ω, rem ω = avg (AvgLMSRB.rho γ H x z θstar r) m ω := by
    intro ω
    simp only [rem, Nat.add_sub_cancel]
    exact AvgLMSRB.avg_rho γ H x z θstar r m ω
  simp only [hrem]
  exact AvgLMSRB.final hA γ hγ0 hγR r m
