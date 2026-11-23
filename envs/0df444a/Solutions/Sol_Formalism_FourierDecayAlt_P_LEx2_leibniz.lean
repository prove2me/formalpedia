-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.leibniz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:06.30324+00:00
-- url     : https://prove2.me/submissions/47f4e259-131c-45f6-84d1-4002d29e8a3e

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_iterDeriv_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_mkP_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_mkP_coeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_ld_rpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_smoothLog_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
open Polynomial
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : Leibniz := by
  intro B A A' T u d hJ hP φ hφ ω a
  obtain ⟨m, c, hc⟩ := hJ
  obtain ⟨c', hc'⟩ := hP
  have hconj : ∀ s : ℝ, conjS B T u s ω a = (mkP m (fun q => c q ω a)).eval (s : ℂ) := by
    intro s
    rw [mkP_eval]
    unfold conjS
    rw [hc _ (smoothLog_rpow s) ω a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ld_rpow q s _ (B.G_pos ω)]
    have h1 : (B.G ω) ^ (-s) * (B.G ω) ^ s = 1 := by
      rw [← Real.rpow_add (B.G_pos ω)]; simp
    have h2 : (((B.G ω) ^ (-s) : ℝ) : ℂ) * (((B.G ω) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, h1]; simp
    push_cast
    linear_combination ((s:ℂ) ^ q * c q ω a) * h2
  have hPP : mkP m (fun q => c q ω a) = mkP d (fun q => c' q ω a) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (s := Set.range (fun s : ℝ => (s : ℂ))) ?_
      (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨s, rfl⟩
    show _ = _
    rw [← hconj s, hc' s ω a, mkP_eval]
  have hdS : ∀ p, dS B T u p ω a = p.factorial * (mkP m (fun q => c q ω a)).coeff p := by
    intro p
    unfold dS
    simp_rw [hconj]
    rw [iterDeriv_poly]
    simp only [Complex.ofReal_zero]
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [Nat.descFactorial_self]
  rw [hc φ hφ ω a]
  have e1 : ∑ q ∈ range (m + 1), (ld q φ (B.G ω) : ℂ) * c q ω a =
      ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q := by
    have hs := Finset.sum_subset (s₁ := range (m+1)) (s₂ := range (max m d + 1))
      (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q)
      (by intro q hq; simp only [Finset.mem_range] at *; omega)
      (by intro q _ hq; rw [mkP_coeff, if_neg (by simpa using hq)]; simp)
    rw [← hs]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [mkP_coeff, if_pos (Finset.mem_range.mp hq)]
  have e2 : ∑ p ∈ range (d + 1), (ld p φ (B.G ω) : ℂ) * dS B T u p ω a / p.factorial =
      ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q := by
    have hs := Finset.sum_subset (s₁ := range (d+1)) (s₂ := range (max m d + 1))
      (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q)
      (by intro q hq; simp only [Finset.mem_range] at *; omega)
      (by intro q _ hq; rw [hPP, mkP_coeff, if_neg (by simpa using hq)]; simp)
    rw [← hs]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hdS]
    have : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    field_simp
  rw [e1, e2]
end Formalism.FourierDecayAlt.P.LEx2
