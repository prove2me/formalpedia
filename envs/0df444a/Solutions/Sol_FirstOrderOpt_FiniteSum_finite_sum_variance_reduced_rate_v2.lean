-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.finite_sum_variance_reduced_rate_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:43:14.755686+00:00
-- url     : https://prove2.me/submissions/e2bf8426-f6e5-40d1-826c-9c991e615b41

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

namespace VRRateD655

lemma V_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : Set E}
    (ν : FirstOrderOpt.Prox.DistanceGeneratingFunction X) {x z : E} (hx : x ∈ X) (hz : z ∈ X) :
    0 ≤ ν.V x z := by
  have h := ν.strongConvex x hx z hz
  unfold FirstOrderOpt.Prox.DistanceGeneratingFunction.V
  nlinarith [sq_nonneg ‖z - x‖]

lemma T_closed (T : ℕ → ℝ) (hT1 : T 1 = 7) (hTrec : ∀ s, 2 ≤ s → T s = 2 * T (s - 1)) :
    ∀ n : ℕ, T (n + 1) = 7 * 2 ^ n := by
  intro n
  induction n with
  | zero => simp [hT1]
  | succ k ih =>
    rw [hTrec (k + 2) (by omega), show k + 2 - 1 = k + 1 by omega, ih, pow_succ]
    ring

lemma W_lower (w : ℕ → ℝ) (hw : ∀ n : ℕ, w (n + 1) = 7 * 2 ^ n / 8 - 3 / 4) :
    ∀ n : ℕ, (2 : ℝ) ^ n / 8 ≤ ∑ s ∈ Finset.Icc 1 (n + 1), w s := by
  intro n
  induction n with
  | zero => simp [hw 0]; norm_num
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), hw (k + 1)]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith

lemma telescope (a b v T : ℕ → ℝ) (γ LQ : ℝ)
    (h : ∀ s, 1 ≤ s → γ * a s + (1 - 4 * LQ * γ) * γ * (T s - 1) * b s + v s ≤
      γ * a (s - 1) + 4 * LQ * γ ^ 2 * T s * b (s - 1) + v (s - 1)) :
    ∀ n : ℕ, ∑ s ∈ Finset.Icc 1 n,
        ((1 - 4 * LQ * γ) * γ * (T s - 1) - 4 * LQ * γ ^ 2 * T (s + 1)) * b s
      + 4 * LQ * γ ^ 2 * T (n + 1) * b n + (γ * a n + v n)
      ≤ γ * a 0 + v 0 + 4 * LQ * γ ^ 2 * T 1 * b 0 := by
  intro n
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    linarith
  | succ k ih =>
    have hk := h (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hk
    rw [Finset.sum_Icc_succ_top (by omega)]
    linarith

end VRRateD655

open MeasureTheory FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (Ψ : E → ℝ) (hΨconv : ConvexOn ℝ X Ψ)
    (LQ : ℝ) (hLQ : 0 < LQ)
    (γ : ℝ) (hγ : γ = 1 / (16 * LQ))
    (T : ℕ → ℝ) (hT1 : T 1 = 7) (hT0 : T 0 = T 1 / 2) (hTrec : ∀ s, 2 ≤ s → T s = 2 * T (s - 1))
    (w : ℕ → ℝ) (hw : ∀ s, 1 ≤ s → w s = (1 - 4 * LQ * γ) * (T (s - 1) - 1) - 4 * LQ * γ * T s)
    (hwpos : ∀ s, 1 ≤ s → 0 < w s)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (S : ℕ) (hS : 1 ≤ S)
    (xtilde : ℕ → Ω → E) (hxtilde : ∀ s, 1 ≤ s → ∀ ω, xtilde s ω ∈ X)
    (x : ℕ → Ω → E) (hx : ∀ s, ∀ ω, x s ω ∈ X)
    (hx0eq : ∀ ω, x 0 ω = x0) (hxtilde0eq : ∀ ω, xtilde 0 ω = x0)
    (hintx : ∀ s, Integrable (fun ω => Ψ (x s ω)) μ)
    (hintxtilde : ∀ s, Integrable (fun ω => Ψ (xtilde s ω)) μ)
    (hintVxs : ∀ s, Integrable (fun ω => ν.V (x s ω) xstar) μ)
    (hepoch : ∀ s, 1 ≤ s →
      γ * (∫ ω, Ψ (x s ω) ∂μ - Ψ xstar) +
        (1 - 4 * LQ * γ) * γ * (T s - 1) * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) +
        ∫ ω, ν.V (x s ω) xstar ∂μ
      ≤ γ * (∫ ω, Ψ (x (s - 1) ω) ∂μ - Ψ xstar) +
        4 * LQ * γ ^ 2 * T s * (∫ ω, Ψ (xtilde (s - 1) ω) ∂μ - Ψ xstar) +
        ∫ ω, ν.V (x (s - 1) ω) xstar ∂μ)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω =
      (∑ s ∈ Finset.Icc 1 S, w s)⁻¹ • ∑ s ∈ Finset.Icc 1 S, w s • xtilde s ω)
    (hint : Integrable (fun ω => Ψ (xbar ω)) μ) :
    ∫ ω, Ψ (xbar ω) ∂μ - Ψ xstar ≤
      (8 / (2 : ℝ) ^ (S - 1)) * ((11 / 4) * (Ψ x0 - Ψ xstar) + 16 * LQ * ν.V x0 xstar) := by
  classical
  -- basic constants
  have hc : 4 * LQ * γ = 1 / 4 := by rw [hγ]; field_simp; ring
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hTc := VRRateD655.T_closed T hT1 hTrec
  have hThalf : ∀ n, T n = T (n + 1) / 2 := by
    intro n
    rcases n with _ | n
    · rw [hT0]
    · rw [hTrec (n + 2) (by omega), show n + 2 - 1 = n + 1 by omega]; ring
  have hTnn : ∀ n, 0 ≤ T n := by
    intro n
    rcases n with _ | n
    · rw [hT0, hT1]; norm_num
    · rw [hTc n]; positivity
  have hwc : ∀ n : ℕ, w (n + 1) = 7 * 2 ^ n / 8 - 3 / 4 := by
    intro n
    rw [hw (n + 1) (by omega), Nat.add_sub_cancel, hThalf n, hTc n, hc]
    ring
  have hwT : ∀ s, 1 ≤ s → w s = T s / 8 - 3 / 4 := by
    intro s hs
    rw [hw s hs, hThalf (s - 1), Nat.sub_add_cancel hs, hc]; ring
  -- nonnegativity facts
  have hconst : ∀ c : ℝ, ∫ _ω, c ∂μ = c := by intro c; simp
  have hb : ∀ s, 1 ≤ s → 0 ≤ ∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar := by
    intro s hs
    have : ∫ _ω, Ψ xstar ∂μ ≤ ∫ ω, Ψ (xtilde s ω) ∂μ :=
      integral_mono (integrable_const _) (hintxtilde s)
        (fun ω => hxstar_opt _ (hxtilde s hs ω))
    rw [hconst] at this; linarith
  have ha : ∀ s, 0 ≤ ∫ ω, Ψ (x s ω) ∂μ - Ψ xstar := by
    intro s
    have : ∫ _ω, Ψ xstar ∂μ ≤ ∫ ω, Ψ (x s ω) ∂μ :=
      integral_mono (integrable_const _) (hintx s) (fun ω => hxstar_opt _ (hx s ω))
    rw [hconst] at this; linarith
  have hv : ∀ s, 0 ≤ ∫ ω, ν.V (x s ω) xstar ∂μ := by
    intro s
    exact integral_nonneg (fun ω => VRRateD655.V_nonneg ν (hx s ω) hxstar)
  have ha0 : ∫ ω, Ψ (x 0 ω) ∂μ = Ψ x0 := by simp [hx0eq]
  have hb0 : ∫ ω, Ψ (xtilde 0 ω) ∂μ = Ψ x0 := by simp [hxtilde0eq]
  have hv0 : ∫ ω, ν.V (x 0 ω) xstar ∂μ = ν.V x0 xstar := by simp [hx0eq]
  -- telescoping
  have htel := VRRateD655.telescope (fun s => ∫ ω, Ψ (x s ω) ∂μ - Ψ xstar)
    (fun s => ∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) (fun s => ∫ ω, ν.V (x s ω) xstar ∂μ) T γ LQ
    hepoch S
  simp only [ha0, hb0, hv0] at htel
  set R := (11 / 4) * (Ψ x0 - Ψ xstar) + 16 * LQ * ν.V x0 xstar with hR
  have hx0X : 0 ≤ Ψ x0 - Ψ xstar := by linarith [hxstar_opt x0 hx0]
  have hV0 : 0 ≤ ν.V x0 xstar := VRRateD655.V_nonneg ν hx0 hxstar
  have hRnn : 0 ≤ R := by rw [hR]; have := hLQ.le; positivity
  have hsumwb : ∑ s ∈ Finset.Icc 1 S, w s * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) ≤ R := by
    have hle : γ * ∑ s ∈ Finset.Icc 1 S, w s * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) ≤
        ∑ s ∈ Finset.Icc 1 S,
          ((1 - 4 * LQ * γ) * γ * (T s - 1) - 4 * LQ * γ ^ 2 * T (s + 1)) *
            (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
      have hbs := hb s hs1
      have hcoef : γ * w s ≤ (1 - 4 * LQ * γ) * γ * (T s - 1) - 4 * LQ * γ ^ 2 * T (s + 1) := by
        have e1 : 4 * LQ * γ ^ 2 = (4 * LQ * γ) * γ := by ring
        rw [e1, hc, hwT s hs1, show T (s + 1) = 2 * T s by rw [hThalf s]; ring]
        nlinarith [hTnn s]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef hbs
    have hextra : 0 ≤ 4 * LQ * γ ^ 2 * T (S + 1) * (∫ ω, Ψ (xtilde S ω) ∂μ - Ψ xstar) := by
      have := hb S hS; have := hTnn (S + 1); have := hLQ.le; positivity
    have hAS : 0 ≤ γ * (∫ ω, Ψ (x S ω) ∂μ - Ψ xstar) + ∫ ω, ν.V (x S ω) xstar ∂μ := by
      have := ha S; have := hv S; positivity
    have hfin : γ * ∑ s ∈ Finset.Icc 1 S, w s * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) ≤ γ * R := by
      have e2 : 4 * LQ * γ ^ 2 * T 1 = (4 * LQ * γ) * γ * T 1 := by ring
      have e3 : γ * (16 * LQ) = 1 := by rw [hγ]; field_simp
      have e5 : 4 * LQ * γ ^ 2 * T 1 * (Ψ x0 - Ψ xstar) = 1 / 4 * γ * 7 * (Ψ x0 - Ψ xstar) := by
        rw [e2, hc, hT1]
      have : γ * R = γ * (Ψ x0 - Ψ xstar) + ν.V x0 xstar + 1 / 4 * γ * 7 * (Ψ x0 - Ψ xstar) := by
        rw [hR]; linear_combination (ν.V x0 xstar) * e3
      rw [this]
      linarith
    exact le_of_mul_le_mul_left hfin hγpos
  -- weights
  set W := ∑ s ∈ Finset.Icc 1 S, w s with hW
  have hWlow : (2 : ℝ) ^ (S - 1) / 8 ≤ W := by
    have := VRRateD655.W_lower w hwc (S - 1)
    rwa [Nat.sub_add_cancel hS] at this
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hWlow
  have h1 : ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s = 1 := by
    rw [← Finset.mul_sum, ← hW, inv_mul_cancel₀ hWpos.ne']
  have hwnn : ∀ s ∈ Finset.Icc 1 S, 0 ≤ W⁻¹ * w s := fun s hs =>
    mul_nonneg (inv_nonneg.mpr hWpos.le) (hwpos s (Finset.mem_Icc.mp hs).1).le
  -- Jensen pointwise
  have hjen : ∀ ω, Ψ (xbar ω) ≤ ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * Ψ (xtilde s ω) := by
    intro ω
    have hxb : xbar ω = ∑ s ∈ Finset.Icc 1 S, (W⁻¹ * w s) • xtilde s ω := by
      rw [hxbar ω, Finset.smul_sum]; simp_rw [smul_smul]
    rw [hxb]
    have := hΨconv.map_sum_le hwnn h1
      (fun s hs => hxtilde s (Finset.mem_Icc.mp hs).1 ω)
    simpa [smul_eq_mul] using this
  have hintsum : Integrable (fun ω => ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * Ψ (xtilde s ω)) μ :=
    integrable_finsetSum _ (fun s _ => (hintxtilde s).const_mul _)
  have hI : ∫ ω, Ψ (xbar ω) ∂μ ≤
      ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * ∫ ω, Ψ (xtilde s ω) ∂μ := by
    calc ∫ ω, Ψ (xbar ω) ∂μ ≤ ∫ ω, ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * Ψ (xtilde s ω) ∂μ :=
          integral_mono hint hintsum hjen
      _ = ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * ∫ ω, Ψ (xtilde s ω) ∂μ := by
          rw [integral_finsetSum _ (fun s _ => (hintxtilde s).const_mul _)]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [integral_const_mul]
  have hE : ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * ∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar =
      W⁻¹ * ∑ s ∈ Finset.Icc 1 S, w s * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) := by
    have : ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * Ψ xstar = Ψ xstar := by
      rw [← Finset.sum_mul, h1, one_mul]
    have e : ∑ s ∈ Finset.Icc 1 S, W⁻¹ * w s * ∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar =
        ∑ s ∈ Finset.Icc 1 S, (W⁻¹ * w s * ∫ ω, Ψ (xtilde s ω) ∂μ - W⁻¹ * w s * Ψ xstar) := by
      rw [Finset.sum_sub_distrib, this]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hstep : ∫ ω, Ψ (xbar ω) ∂μ - Ψ xstar ≤ W⁻¹ * R := by
    have := sub_le_sub_right hI (Ψ xstar)
    rw [hE] at this
    exact this.trans (mul_le_mul_of_nonneg_left hsumwb (inv_nonneg.mpr hWpos.le))
  refine hstep.trans ?_
  have hpow : (0 : ℝ) < 2 ^ (S - 1) := by positivity
  have : W⁻¹ ≤ 8 / (2 : ℝ) ^ (S - 1) := by
    rw [inv_le_comm₀ hWpos (by positivity)]
    calc (8 / (2 : ℝ) ^ (S - 1))⁻¹ = 2 ^ (S - 1) / 8 := by rw [inv_div]
      _ ≤ W := hWlow
  exact mul_le_mul_of_nonneg_right this hRnn
