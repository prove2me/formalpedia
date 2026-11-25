-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.block_of_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:26.759606+00:00
-- url     : https://prove2.me/submissions/d55c9356-a611-49c0-8155-b9199fe6b2af

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_qf_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_psd_iff_qf
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_cross_le

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
theorem _root_.solution : KB.BlockOfCS := by
  intro α β Y₁ Y₂ a w b ha hb hcs
  have ha' := (psd_iff_qf Y₁ a).1 ha
  have hb' := (psd_iff_qf Y₂ b).1 hb
  rw [blockPSD_iff, psd_iff_qf]
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rcases x with p | q <;> rcases y with p' | q'
    · simpa [blockK] using ha'.1 p (by simpa using hx) p' (by simpa using hy)
    · simp [blockK]
    · simp [blockK]
    · simpa [blockK] using hb'.1 q (by simpa using hx) q' (by simpa using hy)
  · rw [qf_block]
    set X := ∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q) with hX
    have hA := ha'.2 (fun p => c (.inl p))
    have hB := hb'.2 (fun q => c (.inr q))
    have h1 := hcs (fun p => conj (c (.inl p))) (fun q => conj (c (.inr q)))
    have eX : (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * conj (conj (c (.inr q))) * w p q) = X := by
      rw [hX]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.conj_conj]
      ring
    have eA : (∑ p ∈ Y₁, ∑ p' ∈ Y₁, conj (c (.inl p)) * conj (conj (c (.inl p'))) * a p p') =
        qf Y₁ a (fun p => c (.inl p)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have eB : (∑ q ∈ Y₂, ∑ q' ∈ Y₂, conj (c (.inr q)) * conj (conj (c (.inr q'))) * b q q') =
        qf Y₂ b (fun q => c (.inr q)) := by
      simp only [qf, Complex.conj_conj]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [eX, eA, eB] at h1
    have hx := cross_le hA hB h1 (norm_nonneg X)
    have hre : -‖X‖ ≤ X.re := by
      have h2 := Complex.normSq_eq_norm_sq X
      rw [Complex.normSq_apply] at h2
      nlinarith [sq_nonneg X.im, norm_nonneg X]
    linarith
end Formalism.FourierDecayAlt.P.PBA
