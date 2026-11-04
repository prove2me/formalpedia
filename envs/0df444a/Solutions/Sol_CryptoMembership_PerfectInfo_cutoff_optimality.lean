-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.cutoff_optimality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:10:28.751212+00:00
-- url     : https://prove2.me/submissions/75b26b6f-5921-45a7-bc78-407924c3636d

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory

namespace CutoffAux

/-- The expected utility factors as `e^{(1-η)x} · C_B`. -/
theorem expUtility_factor (P : Params) (A : ℝ) (B : Set ℝ) (x : ℝ) :
    expUtility P A B x = Real.exp ((1 - P.eta) * x) *
      ∫ ε, B.indicator (fun Aj => Real.exp (P.eta * Aj)) (A + ε) ∂(epsLaw P) := by
  rw [expUtility, ← integral_const_mul]
  congr 1
  funext ε
  by_cases h : A + ε ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, matchUtility, Real.exp_add]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

theorem minerMass_pos (P : Params) (hP : P.Standing) (xi price : ℝ) (hp : 0 < price) :
    0 < minerMass P xi price := by
  obtain ⟨-, -, -, hTe, -, hr1⟩ := hP
  have hve : (P.tauE⁻¹).toNNReal ≠ 0 := by
    simpa [Real.toNNReal_eq_zero, not_le] using hTe
  have hy : 0 < (1 - P.rho) * price := mul_pos (by linarith) hp
  set m := -xi - Real.log ((1 - P.rho) * price)
  have hsub : Set.Ioo m (m + 1) ⊆ {e : ℝ | Real.exp (-(xi + e)) ≤ (1 - P.rho) * price} := by
    intro e he
    simp only [Set.mem_setOf_eq]
    rw [← Real.le_log_iff_exp_le hy]
    have := he.1
    simp only [m] at this
    linarith
  rw [minerMass, minerLaw, measureReal_def]
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  intro h0
  have h1 := gaussianReal_absolutelyContinuous' 0 hve (measure_mono_null hsub h0)
  rw [Real.volume_Ioo] at h1
  simp at h1

end CutoffAux

open CutoffAux in
theorem solution (P : Params) (hP : P.Standing) (A xi : ℝ) :
    (∀ (B : Set ℝ) (price : ℝ), MeasurableSet B → 0 < price →
      (∀ a : ℝ, a ∈ B ↔ price ≤ expUtility P A B a) →
      B = ∅ ∨ ∃ a : ℝ, B = Set.Ici a) ∧
    (∀ (B : Set ℝ) (price : ℝ), IsEquilibrium P A xi B price → ∃ a : ℝ, B = Set.Ici a) := by
  have h1 : ∀ (B : Set ℝ) (price : ℝ), MeasurableSet B → 0 < price →
      (∀ a : ℝ, a ∈ B ↔ price ≤ expUtility P A B a) →
      B = ∅ ∨ ∃ a : ℝ, B = Set.Ici a := by
    intro B p _ hp hh
    simp_rw [expUtility_factor] at hh
    set C := ∫ ε, B.indicator (fun Aj => Real.exp (P.eta * Aj)) (A + ε) ∂(epsLaw P)
    have hC : 0 ≤ C := integral_nonneg (fun ε => Set.indicator_nonneg
      (fun _ _ => (Real.exp_pos _).le) _)
    rcases hC.lt_or_eq with hC | hC
    · right
      have h1 : 0 < 1 - P.eta := by linarith [hP.2.1]
      refine ⟨(Real.log p - Real.log C) / (1 - P.eta), ?_⟩
      ext x
      rw [hh x, Set.mem_Ici, div_le_iff₀ h1,
        ← Real.log_le_log_iff hp (mul_pos (Real.exp_pos _) hC),
        Real.log_mul (Real.exp_pos _).ne' hC.ne', Real.log_exp]
      constructor <;> intro h <;> linarith
    · left
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rw [hh x, ← hC, mul_zero, not_le]
      exact hp
  refine ⟨h1, fun B p heq => ?_⟩
  rcases h1 B p heq.measurableSet heq.price_pos heq.household with h | h
  · exfalso
    have hc := heq.clearing
    rw [h, buyerMass, measureReal_empty] at hc
    linarith [minerMass_pos P hP xi p heq.price_pos]
  · exact h
