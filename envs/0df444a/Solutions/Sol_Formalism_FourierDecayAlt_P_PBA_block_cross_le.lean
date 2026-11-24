-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.block_cross_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:55.022723+00:00
-- url     : https://prove2.me/submissions/3044e101-cbe0-4a1d-af97-8cf5a31e87ef

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_block_quad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {α β : Type} {Y₁ : Finset α} {Y₂ : Finset β} {a : α → α → ℂ} {w : α → β → ℂ}
    {b : β → β → ℂ} (h : KB.BlockPSD Y₁ Y₂ a w b) :
    ‖∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q‖ ≤ ((∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re + (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re) / 2 := by
  have key : ∀ u v : ℂ, 0 ≤ Complex.normSq u * (∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p').re +
      Complex.normSq v * (∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q').re +
      2 * (conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q).re := by
    intro u v
    have h1 := block_quad Y₁ Y₂ h (fun _ => u) (fun _ => v)
    have e1 : qf Y₁ a (fun _ => u) = conj u * u * ∑ p ∈ Y₁, ∑ p' ∈ Y₁, a p p' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e2 : qf Y₂ b (fun _ => v) = conj v * v * ∑ q ∈ Y₂, ∑ q' ∈ Y₂, b q q' := by
      simp only [qf]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    have e3 : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj u * w p q * v) = conj u * v * ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [e1, e2, e3, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h1
    exact h1
  set S := ∑ p ∈ Y₁, ∑ q ∈ Y₂, w p q with hS
  by_cases h0 : S = 0
  · have k1 := key 1 (-1)
    rw [h0] at k1
    simp at k1
    rw [h0, norm_zero]
    simp only [Complex.re_sum]
    linarith
  · have hn : 0 < ‖S‖ := norm_pos_iff.mpr h0
    have k2 := key S (-(‖S‖ : ℂ))
    have hns : Complex.normSq S = ‖S‖ ^ 2 := Complex.normSq_eq_norm_sq S
    have hnr : Complex.normSq (-(‖S‖ : ℂ)) = ‖S‖ ^ 2 := by
      rw [Complex.normSq_neg, Complex.normSq_ofReal]
      ring
    have hcr : (conj S * -(‖S‖ : ℂ) * S).re = -(‖S‖ ^ 3) := by
      have e : conj S * -(‖S‖ : ℂ) * S = -((‖S‖ : ℂ) * (Complex.normSq S : ℂ)) := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      rw [e, hns, Complex.neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
      ring
    rw [hns, hnr, hcr] at k2
    nlinarith [mul_pos hn hn, k2]
end Formalism.FourierDecayAlt.P.PBA
