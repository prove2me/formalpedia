-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.concavity_equidistribution
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:46.244398+00:00
-- url     : https://prove2.me/submissions/201258d5-5892-4aef-9803-e1c3df02df91

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OrthogonalMinorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset Matrix
open scoped ComplexOrder
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : ConcavityEquidistribution := by
  intro ι σ _ _ _ _ π c y B hfib hy hB
  classical
  have hcardσ : (Fintype.card σ : ℝ) = c * Fintype.card ι := by
    have h := Finset.card_eq_sum_card_fiberwise (f := π) (s := (univ : Finset σ))
      (t := (univ : Finset ι)) (fun _ _ => Finset.mem_coe.2 (mem_univ _))
    simp only [hfib, sum_const, smul_eq_mul, card_univ] at h
    rw [h]; push_cast; ring
  have hσpos : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℝ) < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hcardσ; simp at hcardσ
    · exact_mod_cast h
  have hι : (0 : ℝ) < Fintype.card ι := by
    have : (0 : ℝ) < c * Fintype.card ι := hcardσ ▸ hσpos
    exact (pos_iff_pos_of_mul_pos this).1 hc
  have hsum : ∑ s, Real.log (y (π s)) = c * ∑ τ, Real.log (y τ) := by
    have h := Finset.sum_fiberwise (s := (univ : Finset σ)) (g := π)
      (f := fun s => Real.log (y (π s)))
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.log (y τ))
      (fun s hs => by rw [(mem_filter.1 hs).2])]
    rw [sum_const, hfib, nsmul_eq_mul]
  have hw : ∑ _τ : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := (univ : Finset ι))
    (w := fun _ => (Fintype.card ι : ℝ)⁻¹) (p := y) (fun _ _ => by positivity) hw
    (fun τ _ => hy τ)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hSpos : 0 < ∑ τ, y τ := by
    have : Nonempty ι := ⟨π (Classical.arbitrary σ)⟩
    exact Finset.sum_pos (fun τ _ => hy τ) univ_nonempty
  unfold mean
  rw [hsum, hcardσ]
  calc (c * ∑ τ, Real.log (y τ)) / (c * Fintype.card ι)
      = (Fintype.card ι : ℝ)⁻¹ * ∑ τ, Real.log (y τ) := by field_simp
    _ ≤ Real.log ((Fintype.card ι : ℝ)⁻¹ * ∑ τ, y τ) := hj
    _ ≤ Real.log (B / Fintype.card ι) := by
        apply Real.log_le_log (by positivity)
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hB (by positivity)
end Formalism.HermitianLattices.TraceIntegrality
