-- Prove2me | solution 1 for GaussianMatrix.pinv_frobenius_tail
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T05:08:15.232129+00:00
-- url     : https://prove2.me/submissions/9545f024-a11a-4ca1-b1c6-360b14efe4cc

import Definitions.Def_GaussianMatrix_basic
import Theorems.Thm_GaussianMatrix_inverse_wishart_diag_law
import Theorems.Thm_GaussianMatrix_inv_chi_square_Lq_bound

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Deterministic identity: `‖G†‖_F² = tr((G Gᵀ)⁻¹)` for every real matrix `G`
(both sides vanish when `G Gᵀ` is singular, by Mathlib's convention `A⁻¹ = 0`). -/
theorem pft_frobSq_pinvR_eq_trace_inv {r k : ℕ} (G : Matrix (Fin r) (Fin k) ℝ) :
    frobSq (pinvR G) = ∑ i, (G * Gᵀ)⁻¹ i i := by
  set A : Matrix (Fin r) (Fin r) ℝ := G * Gᵀ with hA
  set M : Matrix (Fin r) (Fin r) ℝ := A⁻¹ with hM
  have hAt : Aᵀ = A := by rw [hA, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMt : Mᵀ = M := by rw [hM, Matrix.transpose_nonsing_inv, hAt]
  have hkey : (pinvR G)ᵀ * pinvR G = M := by
    unfold pinvR
    rw [← hA, ← hM, Matrix.transpose_mul, Matrix.transpose_transpose, hMt]
    by_cases h : IsUnit A.det
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc G, ← hA, hM, Matrix.mul_nonsing_inv A h,
        Matrix.mul_one]
    · have h0 : M = 0 := by rw [hM]; exact Matrix.nonsing_inv_apply_not_isUnit A h
      rw [h0]; simp
  have htr : frobSq (pinvR G) = Matrix.trace ((pinvR G)ᵀ * pinvR G) := by
    unfold frobSq Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [sq]
  rw [htr, hkey]
  rfl

lemma pft_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

/-- HMT Lemma A.10 (endpoint case) in `eLpNorm` form: `E_q(Ξ⁻¹) ≤ 3/d` for `q = (d-1)/2`. -/
lemma pft_eLpNorm_inv_chi {d : ℕ} (hd : 5 ≤ d) :
    eLpNorm (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹) (ENNReal.ofReal (((d : ℝ) - 1) / 2))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤ ENNReal.ofReal (3 / d) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : 0 < ((d : ℝ) - 1) / 2 := by linarith
  obtain ⟨hint, hlt⟩ := inv_chi_square_Lq_bound hd
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  have hnn : ∀ x : Fin d → ℝ, 0 ≤ (∑ j, x j ^ 2)⁻¹ :=
    fun x => inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have h1 : ∀ x : Fin d → ℝ, ‖(∑ j, x j ^ 2)⁻¹‖ₑ ^ (((d : ℝ) - 1) / 2)
      = ENNReal.ofReal (((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2)) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn x), ENNReal.ofReal_rpow_of_nonneg (hnn x) hq.le]
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hnn x) _)]
  have hI : 0 ≤ ∫ x, ((∑ j, x j ^ 2)⁻¹) ^ (((d : ℝ) - 1) / 2)
      ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    integral_nonneg fun x => Real.rpow_nonneg (hnn x) _
  rw [ENNReal.ofReal_rpow_of_nonneg hI (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h3 : (0 : ℝ) ≤ 3 / d := by positivity
  calc _ ≤ ((3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2)) ^ (1 / (((d : ℝ) - 1) / 2)) :=
        Real.rpow_le_rpow hI hlt.le (by positivity)
    _ = 3 / d := by
        rw [← Real.rpow_mul h3, mul_one_div_cancel hq.ne', Real.rpow_one]

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hrk : r + 4 ≤ k) (t : ℝ) (ht : 1 ≤ t) :
    (gaussianMatrix r k) {G | 12 * (r : ℝ) / ((k : ℝ) - r) * t < frobSq (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal (4 * t ^ (-(((k : ℝ) - r) / 2))) := by
  have hrk' : (r : ℝ) + 4 ≤ k := by exact_mod_cast hrk
  have hp : (4 : ℝ) ≤ (k : ℝ) - r := by linarith
  have hq : (2 : ℝ) ≤ ((k : ℝ) - r) / 2 := by linarith
  have hq0 : (0 : ℝ) < ((k : ℝ) - r) / 2 := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  -- the case r = 0: the event is empty
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    have : {G : Fin 0 → Fin k → ℝ | 12 * ((0 : ℕ) : ℝ) / ((k : ℝ) - (0 : ℕ)) * t
        < frobSq (pinvR (Matrix.of G))} = ∅ := by
      ext G; simp [frobSq]
    rw [this, measure_empty]
    exact zero_le
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
  set μ := gaussianMatrix r k with hμ
  set Q : ENNReal := ENNReal.ofReal (((k : ℝ) - r) / 2) with hQ
  have hQ0 : Q ≠ 0 := by simpa [hQ] using hq0
  have hQtop : Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact ENNReal.one_le_ofReal.mpr (by linarith)
  have hQr : Q.toReal = ((k : ℝ) - r) / 2 := ENNReal.toReal_ofReal hq0.le
  set D : Fin r → (Fin r → Fin k → ℝ) → ℝ :=
    fun i G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hD
  have hDm : ∀ i, Measurable (D i) := fun i => pft_measurable_inv_entry i i
  have hZ : ∀ G : Fin r → Fin k → ℝ, frobSq (pinvR (Matrix.of G)) = (∑ i, D i) G := by
    intro G
    rw [pft_frobSq_pinvR_eq_trace_inv, Finset.sum_apply]
  -- each diagonal entry is `1/χ²_{k-r+1}` in law; its `L^q` norm is at most `3/(k-r+1)`
  have hdcast : ((k - r + 1 : ℕ) : ℝ) = (k : ℝ) - r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
  have hDi : ∀ i, eLpNorm (D i) Q μ ≤ ENNReal.ofReal (3 / ((k : ℝ) - r + 1)) := by
    intro i
    have hlaw := inverse_wishart_diag_law (by omega : r ≤ k) i
    have e1 : eLpNorm (D i) Q μ = eLpNorm id Q (Measure.map (D i) μ) := by
      rw [eLpNorm_map_measure aestronglyMeasurable_id (hDm i).aemeasurable]; rfl
    have hS : Measurable (fun x : Fin (k - r + 1) → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
    rw [e1, hD, hlaw, eLpNorm_map_measure aestronglyMeasurable_id hS.aemeasurable]
    have := pft_eLpNorm_inv_chi (d := k - r + 1) (by omega)
    rw [hdcast, show (k : ℝ) - r + 1 - 1 = (k : ℝ) - r by ring] at this
    exact this
  -- Minkowski's inequality in `L^q`
  have hmink : eLpNorm (∑ i, D i) Q μ ≤ ENNReal.ofReal (r * (3 / ((k : ℝ) - r + 1))) := by
    refine (eLpNorm_sum_le (fun i _ => (hDm i).aestronglyMeasurable) hQ1).trans ?_
    calc ∑ i, eLpNorm (D i) Q μ ≤ ∑ _i : Fin r, ENNReal.ofReal (3 / ((k : ℝ) - r + 1)) :=
          Finset.sum_le_sum fun i _ => hDi i
      _ = ENNReal.ofReal (r * (3 / ((k : ℝ) - r + 1))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  -- Markov's inequality
  set a : ℝ := 12 * (r : ℝ) / ((k : ℝ) - r) * t with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hsub : {G : Fin r → Fin k → ℝ | a < frobSq (pinvR (Matrix.of G))}
      ⊆ {G | ENNReal.ofReal a ≤ ‖(∑ i, D i) G‖ₑ} := by
    intro G hG
    simp only [Set.mem_ofPred_eq] at hG ⊢
    rw [hZ] at hG
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hG.le.trans (le_abs_self _))
  have hSm : Measurable (∑ i, D i) := by
    have := Finset.measurable_sum (Finset.univ : Finset (Fin r)) fun i _ => hDm i
    simpa only [← Finset.sum_apply] using this
  have hmarkov := meas_ge_le_mul_pow_eLpNorm_enorm μ hQ0 hQtop hSm.aestronglyMeasurable
    (ε := ENNReal.ofReal a) (by simpa using ha0) (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [hQr] at hmarkov
  have hc : (0 : ℝ) ≤ r * (3 / ((k : ℝ) - r + 1)) := by positivity
  calc μ {G | a < frobSq (pinvR (Matrix.of G))}
      ≤ μ {G | ENNReal.ofReal a ≤ ‖(∑ i, D i) G‖ₑ} := measure_mono hsub
    _ ≤ (ENNReal.ofReal a)⁻¹ ^ (((k : ℝ) - r) / 2) *
          eLpNorm (∑ i, D i) Q μ ^ (((k : ℝ) - r) / 2) := hmarkov
    _ ≤ (ENNReal.ofReal a)⁻¹ ^ (((k : ℝ) - r) / 2) *
          ENNReal.ofReal (r * (3 / ((k : ℝ) - r + 1))) ^ (((k : ℝ) - r) / 2) := by
        gcongr
    _ = ENNReal.ofReal ((a⁻¹ * (r * (3 / ((k : ℝ) - r + 1)))) ^ (((k : ℝ) - r) / 2)) := by
        rw [← ENNReal.ofReal_inv_of_pos ha0, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
          ENNReal.ofReal_rpow_of_nonneg hc hq0.le, ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow (by positivity) hc]
    _ ≤ ENNReal.ofReal (4 * t ^ (-(((k : ℝ) - r) / 2))) := by
        apply ENNReal.ofReal_le_ofReal
        have hp0 : (0 : ℝ) < (k : ℝ) - r := by linarith
        have hx : a⁻¹ * (r * (3 / ((k : ℝ) - r + 1))) ≤ t⁻¹ := by
          rw [ha]
          have hr0 : (0 : ℝ) < r := by linarith
          rw [show (12 * (r : ℝ) / ((k : ℝ) - r) * t)⁻¹ * (r * (3 / ((k : ℝ) - r + 1)))
              = ((k : ℝ) - r) / (4 * ((k : ℝ) - r + 1)) * t⁻¹ by field_simp; ring]
          have : ((k : ℝ) - r) / (4 * ((k : ℝ) - r + 1)) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          have hti : 0 < t⁻¹ := inv_pos.mpr ht0
          nlinarith
        calc (a⁻¹ * (r * (3 / ((k : ℝ) - r + 1)))) ^ (((k : ℝ) - r) / 2)
            ≤ t⁻¹ ^ (((k : ℝ) - r) / 2) := Real.rpow_le_rpow (by positivity) hx hq0.le
          _ = t ^ (-(((k : ℝ) - r) / 2)) := by rw [Real.inv_rpow ht0.le, Real.rpow_neg ht0.le]
          _ ≤ 4 * t ^ (-(((k : ℝ) - r) / 2)) := by
              have : 0 ≤ t ^ (-(((k : ℝ) - r) / 2)) := Real.rpow_nonneg ht0.le _
              linarith
