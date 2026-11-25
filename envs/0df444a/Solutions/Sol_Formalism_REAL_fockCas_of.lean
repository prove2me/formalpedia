-- Prove2me | solution 1 for Formalism.REAL.fockCas_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:41.182531+00:00
-- url     : https://prove2.me/submissions/fc61c308-7ca3-499d-91c7-b4eb4cc8925c

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_casimir_bilinearLeft
import Theorems.Thm_Formalism_REAL_casimir_bilinearRight_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (h : CCR) : FockCas := by
  intro M n' ε ε'
  have hBP : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (h M n' ε ε' i j a b).1
  have hBB : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (h M n' ε ε' i j a b).2.1
  have hEg : Eg ε ε' = bilinearLeft (bop ε ε') (bpl ε ε') := by
    funext i j
    rfl
  have hEg' : Eg' ε ε' = fun a b => -bilinearRight (bop ε ε') (bpl ε ε') a b := by
    funext a b
    rfl
  have hNN : NN ε ε' = bilinearNumber (bop ε ε') (bpl ε ε') := rfl
  refine ⟨?_, ?_⟩
  · simp only [NN, Eg, Eg', Finset.sum_neg_distrib, neg_neg]
    exact Finset.sum_comm
  · have hc : Cas (Eg' ε ε') = ∑ a, ∑ b,
        bilinearRight (bop ε ε') (bpl ε ε') a b * bilinearRight (bop ε ε') (bpl ε ε') b a := by
      rw [hEg']
      simp only [Cas, neg_mul_neg]
    rw [hc, casimir_bilinearRight_sum hBP hBB, hEg, casimir_bilinearLeft hBP, hNN, Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul]
    abel
end Formalism.REAL
