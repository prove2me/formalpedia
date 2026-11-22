-- Prove2me | solution 1 for BurkholderDFI.SquareFnLp.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:04:05.471904+00:00
-- url     : https://prove2.me/submissions/f833a6c8-cebc-4d66-a6ce-9b601b04068c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale
import Theorems.Thm_BurkholderDFI_SquareFnLp_eq_3_7
import Theorems.Thm_BurkholderDFI_SquareFnLp_duality_bound

set_option autoImplicit false

namespace BurkholderDFI.SquareFnLp.Thm32Proof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp
open scoped ENNReal NNReal

variable {Ω : Type*}

theorem measurable_dseq [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (k : ℕ) : Measurable (dseq g k) := by
  by_cases h0 : k = 0
  · subst h0
    have : dseq g 0 = fun _ => (0 : ℝ) := by funext ω; simp [dseq]
    rw [this]
    exact measurable_const
  by_cases h1 : k = 1
  · subst h1
    have : dseq g 1 = g 1 := by funext ω; simp [dseq]
    rw [this]
    exact hg 1
  · have : dseq g k = fun ω => g k ω - g (k - 1) ω := by funext ω; simp [dseq, h0, h1]
    rw [this]
    exact (hg k).sub (hg (k - 1))

theorem measurable_sqFnN [MeasurableSpace Ω] {g : ℕ → Ω → ℝ} (hg : ∀ k, Measurable (g k))
    (n : ℕ) : Measurable (sqFnN g n) := by
  unfold sqFnN
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  exact Finset.measurable_sum _ fun k _ => (measurable_dseq hg k).pow_const 2

theorem lpNormE_mono [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    {A B : Ω → ℝ≥0∞} (h : ∀ ω, A ω ≤ B ω) : lpNormE P p A ≤ lpNormE P p B := by
  unfold lpNormE
  exact ENNReal.rpow_le_rpow (lintegral_mono fun ω => ENNReal.rpow_le_rpow (h ω) hp.le)
    (by positivity)

theorem sqFnN_mono (g : ℕ → Ω → ℝ) {n m : ℕ} (h : n ≤ m) (ω : Ω) :
    sqFnN g n ω ≤ sqFnN g m ω := by
  unfold sqFnN
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
    fun _ _ _ => sq_nonneg _

theorem rpow_iSup (r : ℝ) (hr : 0 < r) (x : ℕ → ℝ≥0∞) :
    (⨆ n, x n) ^ r = ⨆ n, x n ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iSup x

/-- Monotone convergence for `‖·‖_p`: `‖sup_n S_n‖_p = sup_n ‖S_n‖_p`. -/
theorem lpNormE_iSup [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ} (hp : 0 < p)
    (S : ℕ → Ω → ℝ≥0∞) (hS : ∀ n, Measurable (S n)) (hmono : Monotone S) :
    lpNormE P p (fun ω => ⨆ n, S n ω) = ⨆ n, lpNormE P p (S n) := by
  unfold lpNormE
  simp_rw [rpow_iSup p hp]
  rw [lintegral_iSup (fun n => (hS n).pow_const p)
    (fun n m h ω => ENNReal.rpow_le_rpow (hmono h ω) hp.le)]
  exact rpow_iSup (1 / p) (by positivity) _

end BurkholderDFI.SquareFnLp.Thm32Proof

open MeasureTheory ProbabilityTheory Filter Topology BurkholderDFI.SquareFnLp
  BurkholderDFI.SquareFnLp.Thm32Proof
open scoped ENNReal NNReal

theorem solution (p : ℝ) (hp : 1 < p) :
    ∃ c C : ℝ≥0, 0 < c ∧ 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P →
        (c : ℝ≥0∞) * lpNormE P p (sqFn f) ≤ pNorm P p f ∧
          pNorm P p f ≤ (C : ℝ≥0∞) * lpNormE P p (sqFn f) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq : 0 < p / (p - 1) := div_pos hp0 hp1
  have hpq : p⁻¹ + (p / (p - 1))⁻¹ = 1 := by
    rw [inv_div]
    field_simp
    ring
  have hK : 0 < 18 * Real.sqrt p * (p / (p - 1)) := by positivity
  have hL : 0 < 18 * Real.sqrt (p / (p - 1)) * p := by
    have : 0 < Real.sqrt (p / (p - 1)) := Real.sqrt_pos.mpr hq
    positivity
  have hKnn : (Real.toNNReal (18 * Real.sqrt p * (p / (p - 1)))) ≠ 0 :=
    (Real.toNNReal_pos.mpr hK).ne'
  refine ⟨(Real.toNNReal (18 * Real.sqrt p * (p / (p - 1))))⁻¹,
    Real.toNNReal (18 * Real.sqrt (p / (p - 1)) * p),
    inv_pos.mpr (Real.toNNReal_pos.mpr hK), Real.toNNReal_pos.mpr hL, ?_⟩
  intro Ω mΩ P _ ℱ f hf
  have hfm : ∀ k, Measurable (f k) := fun k => ((hf.1 k).mono (ℱ.le k)).measurable
  have hle_sq : ∀ n ω, sqFnN f n ω ≤ sqFn f ω := fun n ω =>
    le_iSup (fun n => sqFnN f n ω) n
  constructor
  · -- `‖S(f)‖_p ≤ 18 p^{1/2} q ‖f‖_p`, by (3.7) and monotone convergence.
    have hSn : ∀ n, lpNormE P p (sqFnN f n)
        ≤ ENNReal.ofReal (18 * Real.sqrt p * (p / (p - 1))) * pNorm P p f := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hz : sqFnN f 0 = fun _ => 0 := by
          funext ω
          simp [sqFnN]
        rw [hz]
        unfold lpNormE
        simp [ENNReal.zero_rpow_of_pos hp0, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp0)]
      · refine (eq_3_7 hf n hn p (p / (p - 1)) hp hpq).trans (mul_le_mul' le_rfl ?_)
        exact le_iSup₂ (f := fun n (_ : n ∈ Set.Ici (1 : ℕ)) =>
          lpNormE P p (fun ω => ENNReal.ofReal |f n ω|)) n (Set.mem_Ici.mpr hn)
    have hS : lpNormE P p (sqFn f)
        ≤ ENNReal.ofReal (18 * Real.sqrt p * (p / (p - 1))) * pNorm P p f := by
      have heq : sqFn f = fun ω => ⨆ n, sqFnN f n ω := rfl
      rw [heq, lpNormE_iSup P hp0 _ (measurable_sqFnN hfm)
        (fun n m h ω => sqFnN_mono f h ω)]
      exact iSup_le hSn
    calc ((Real.toNNReal (18 * Real.sqrt p * (p / (p - 1))))⁻¹ : ℝ≥0) * lpNormE P p (sqFn f)
        ≤ ((Real.toNNReal (18 * Real.sqrt p * (p / (p - 1))))⁻¹ : ℝ≥0)
            * (ENNReal.ofReal (18 * Real.sqrt p * (p / (p - 1))) * pNorm P p f) :=
          mul_le_mul' le_rfl hS
      _ = pNorm P p f := by
          rw [← mul_assoc, ENNReal.coe_inv hKnn, ENNReal.ofReal,
            ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hKnn) ENNReal.coe_ne_top, one_mul]
  · -- `‖f‖_p ≤ 18 q^{1/2} p ‖S(f)‖_p`, by the duality bound and `S_n(f) ≤ S(f)`.
    refine iSup₂_le fun n hn => ?_
    refine (duality_bound hf n (Set.mem_Ici.mp hn) p (p / (p - 1)) hp hpq).trans ?_
    exact mul_le_mul' le_rfl (lpNormE_mono P hp0 (hle_sq n))
