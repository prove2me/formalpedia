-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.vecD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:51:40.53551+00:00
-- url     : https://prove2.me/submissions/a5f840e6-4f62-4153-851c-b14663165eff

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → A)
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (hE : GlRel E) (y : Fin (N + 1) → A) (hy : IsVec E y) : IsVec E (fun l => ∑ c, E c l * y c) := by
  intro a b l
  have h1 : ∀ c, E a b * (E c l * y c) - E c l * y c * E a b =
      ((if b = c then E a l else 0) - (if l = a then E c b else 0)) * y c + E c l * (if a = c then -y b else 0) := by
    intro c
    rw [← hE a b c l, ← hy a b c]
    noncomm_ring
  simp only []
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [h1, sub_mul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hal : a = l
  · subst hal
    simp only [if_true, mul_neg]
    abel
  · rw [if_neg hal]
    simp [Ne.symm hal]
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
