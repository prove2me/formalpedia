-- Prove2me | solution 1 for BesbesZeevi.Parametric.parametric_regret_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:38:21.176344+00:00
-- url     : https://prove2.me/submissions/8d1e89a3-7d8e-40b9-b468-2d9669e4b178
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm
import Theorems.Thm_BesbesZeevi_Parametric_a25
set_option autoImplicit false

open MeasureTheory

namespace BesbesZeevi.Parametric

theorem c2_tau_rate (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℕ → ℝ,
      (∀ n : ℕ, n0 ≤ n → c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ n : ℕ, 2 ≤ n → n0 ≤ n →
        τ n + Real.sqrt (Real.log (n : ℝ)) / Real.sqrt ((n : ℝ) * τ n)
          ≤ K * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hc' : 0 < c' := lt_of_lt_of_le hc hcc'
  have hl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨1 / Real.sqrt c + c' / Real.sqrt (Real.log 2), by positivity, fun τ hτ n hn hn0 => ?_⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hapos : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnpos _
  have hneg : (n : ℝ) ^ (-(1 : ℝ) / 3) = ((n : ℝ) ^ ((1 : ℝ) / 3))⁻¹ := by
    rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring]
    exact Real.rpow_neg hnpos.le _
  have ha3 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  obtain ⟨hτl, hτu⟩ := hτ n hn0
  rw [hneg] at hτl hτu
  have hs : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) hnR)
  set a := (n : ℝ) ^ ((1 : ℝ) / 3) with ha
  set l2 := Real.sqrt (Real.log 2) with hl2def
  set s := Real.sqrt (Real.log n) with hsdef
  have hspos : 0 < s := lt_of_lt_of_le hl2 hs
  have e : c * a ^ 2 ≤ (n : ℝ) * τ n := by
    rw [← ha3]
    have : c * a ^ 2 = a ^ 3 * (c * a⁻¹) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hτl (by positivity)
  have hsq : Real.sqrt c * a ≤ Real.sqrt ((n : ℝ) * τ n) := by
    rw [show Real.sqrt c * a = Real.sqrt (c * a ^ 2) by
      rw [Real.sqrt_mul hc.le, Real.sqrt_sq hapos.le]]
    exact Real.sqrt_le_sqrt e
  have h2 : s / Real.sqrt ((n : ℝ) * τ n) ≤ s * ((1 / Real.sqrt c) / a) := by
    rw [div_div, div_eq_mul_one_div s]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hsq) hspos.le
  have hratio : 1 ≤ s / l2 := by rw [le_div_iff₀ hl2]; linarith
  have hτ2 : τ n ≤ c' / l2 * s / a := by
    have : c' / l2 * s / a = c' * a⁻¹ * (s / l2) := by field_simp
    rw [this]
    calc τ n ≤ c' * a⁻¹ := hτu
      _ = c' * a⁻¹ * 1 := by ring
      _ ≤ c' * a⁻¹ * (s / l2) := mul_le_mul_of_nonneg_left hratio (by positivity)
  have hK : (1 / Real.sqrt c + c' / l2) * s / a = s * ((1 / Real.sqrt c) / a) + c' / l2 * s / a := by
    ring
  rw [hK]; linarith

theorem c2_jDetScaled_nonneg {k : ℕ} (D : Market) (F : Family k D)
    (θ : Fin k → ℝ) (hθ : θ ∈ F.Θ) (n : ℕ) : 0 ≤ jDetScaled D F θ n := by
  unfold jDetScaled jDet
  have h0 : F.demand D.pOff θ = 0 := (F.regular θ hθ).1
  have hmem : (0 : ℝ) ∈ {v : ℝ | ∃ p : ℝ → ℝ,
      DetFeasible D (fun p => (n : ℝ) * F.demand p θ) ((n : ℝ) * D.x) p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * ((n : ℝ) * F.demand (p t) θ)} := by
    refine ⟨fun _ => D.pOff, ⟨measurable_const, fun _ _ => Or.inr rfl, ?_, ?_, ?_⟩, ?_⟩
    · simp [h0]
    · simp [h0]
    · simp only [h0, mul_zero, integral_zero]
      exact mul_nonneg (Nat.cast_nonneg _) D.x_pos.le
    · simp [h0]
  by_cases hb : BddAbove {v : ℝ | ∃ p : ℝ → ℝ,
      DetFeasible D (fun p => (n : ℝ) * F.demand p θ) ((n : ℝ) * D.x) p ∧
      v = ∫ t in Set.Icc (0 : ℝ) D.T, p t * ((n : ℝ) * F.demand (p t) θ)}
  · exact le_csSup hb hmem
  · rw [Real.sSup_of_not_bddAbove hb]

theorem c2_regret_le_one {k : ℕ} (D : Market) (F : Family k D) (S : OptimizerSelection D F)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (N : PoissonProcess Ω P) (n : ℕ)
    (θ : Fin k → ℝ) (hθ : θ ∈ F.Θ) (τ : ℝ) :
    regret F S N n θ τ ≤ 1 := by
  unfold regret
  have h1 : 0 ≤ jPolicy F S N n θ τ := ENNReal.toReal_nonneg
  have h2 := c2_jDetScaled_nonneg D F θ hθ n
  have : 0 ≤ jPolicy F S N n θ τ / jDetScaled D F θ n := div_nonneg h1 h2
  linarith

/-- The reduction: Proposition 3 follows from (A-25) by the tuning-rate arithmetic. -/
theorem c2_parent_of_a25 {k : ℕ} (D : Market) (F : Family k D)
    (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ)
    (ha25 : ∃ C3 : ℝ, 0 < C3 ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C3 / (D.m * min D.T (D.x / D.M)) *
            (τ n + Real.sqrt (Real.log (n : ℝ)) /
              Real.sqrt ((n : ℝ) * τ n))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by
  obtain ⟨C3, hC3, hA⟩ := ha25
  obtain ⟨K, hK, hT⟩ := c2_tau_rate c c' hc hcc' n0
  have hApos : 0 < D.m * min D.T (D.x / D.M) :=
    mul_pos D.m_pos (lt_min D.T_pos (div_pos D.x_pos D.M_pos))
  have hl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  set B := C3 / (D.m * min D.T (D.x / D.M)) with hB
  have hBpos : 0 < B := div_pos hC3 hApos
  set E := (n0 : ℝ) ^ ((1 : ℝ) / 3) / Real.sqrt (Real.log 2) + 1 with hE
  have hEpos : 0 < E := by positivity
  refine ⟨max (B * K) E, lt_of_lt_of_le hEpos (le_max_right _ _),
    fun S τ hτ1 hτ2 Ω _ P N n hn θ hθ => ?_⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hapos : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hnpos _
  have hs : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) hnR)
  have hspos : 0 < Real.sqrt (Real.log n) := lt_of_lt_of_le hl2 hs
  rcases le_or_gt n0 n with hn0 | hn0
  · calc regret F S N n θ (τ n)
        ≤ B * (τ n + Real.sqrt (Real.log (n : ℝ)) / Real.sqrt ((n : ℝ) * τ n)) :=
          hA S τ hτ1 hτ2 Ω P N n hn θ hθ
      _ ≤ B * (K * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left (hT τ hτ2 n hn hn0) hBpos.le
      _ = (B * K) * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by ring
      _ ≤ max (B * K) E * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by
          apply div_le_div_of_nonneg_right _ hapos.le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hspos.le
  · have hreg := c2_regret_le_one D F S N n θ hθ (τ n)
    have hle : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (n0 : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hn0.le) (by norm_num)
    have hEl : (n0 : ℝ) ^ ((1 : ℝ) / 3) ≤ E * Real.sqrt (Real.log 2) := by
      rw [hE, add_mul, div_mul_cancel₀ _ hl2.ne']; linarith
    have h1 : 1 ≤ E * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [le_div_iff₀ hapos, one_mul]
      have : E * Real.sqrt (Real.log 2) ≤ E * Real.sqrt (Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hs hEpos.le
      linarith
    have h2 : E * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) ≤
        max (B * K) E * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by
      apply div_le_div_of_nonneg_right _ hapos.le
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hspos.le
    linarith

end BesbesZeevi.Parametric

open MeasureTheory BesbesZeevi.Parametric in
theorem solution {k : ℕ} (D : Market) (F : Family k D)
    (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) :=
  c2_parent_of_a25 D F c c' hc hcc' n0 (a25 D F c c' hc hcc' n0)
