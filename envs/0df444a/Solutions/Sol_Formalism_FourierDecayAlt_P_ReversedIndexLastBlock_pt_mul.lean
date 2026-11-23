-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.pt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:09.653798+00:00
-- url     : https://prove2.me/submissions/c1803211-7625-4c90-85b6-d1318f4f2993

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_revIn_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_revIn_revIn
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_blk_revIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
open Formalism.DoubleCosetMeasures
namespace Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
theorem _root_.solution {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ) :
    pt s t * pt s (fun b => (t b)⁻¹) = (1 : Matrix (Fin s.sum) (Fin s.sum) K) := by
  ext a c
  simp only [Matrix.mul_apply, pt]
  rw [Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]
  · rw [if_pos rfl]
    simp only [Fin.val_mk]
    rw [revIn_revIn s a a.2, blk_revIn s a a.2, Matrix.one_apply]
    by_cases h : c = a
    · subst h
      simp
    · have h' : (c : ℕ) ≠ a := fun e => h (Fin.ext e)
      simp [h', Ne.symm h]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro e
    exact hb (Fin.ext e)
  · simp
end Formalism.FourierDecayAlt.P.ReversedIndexLastBlock
