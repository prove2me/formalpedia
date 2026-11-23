-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.psd_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:53.904162+00:00
-- url     : https://prove2.me/submissions/3ed90198-5fde-4462-9fe1-f1288a8b00c5

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_sum_of_classes
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {T : Type} [Fintype T] (r : Setoid T) (N : T → T → ℕ)
    (h0 : ∀ i j, ¬ r i j → N i j = 0) (h1 : ∀ i j k, r i j → r i k → N i j = N k k)
    (c : T → ℂ) :
    (∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ)).re := by
  classical
  have key : ∑ i, ∑ j, c i * conj (c j) * (N i j : ℂ) =
      ((∑ κ : Quotient r, ((N κ.out κ.out : ℕ) : ℝ) *
        Complex.normSq (∑ i, if (Quotient.mk r i) = κ then c i else 0) : ℝ) : ℂ) := by
    rw [← sum_of_classes (fun i => Quotient.mk r i) (fun κ => ((N κ.out κ.out : ℕ) : ℝ)) c]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    by_cases h : r i j
    · rw [if_pos (Quotient.sound h),
        h1 i j (Quotient.mk r i).out h (Setoid.symm (Quotient.mk_out i))]
      simp
    · rw [if_neg (fun e => h (Quotient.exact e)), h0 i j h]
      simp
  rw [key]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact Finset.sum_nonneg fun κ _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
end Formalism.FourierDecayAlt.P.A5x4
