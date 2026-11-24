-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.peel_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:24:45.58274+00:00
-- url     : https://prove2.me/submissions/d593e140-b898-44f1-981d-d2ff4c5973d7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sign_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {m : ℕ} (I : Ideal A) {ι : Type} [Fintype ι] (η : ι → ℂ) (Q : Fin (m + 1) → A)
    (T : Fin (m + 1) → ι → A) (κ : ℂ)
    (hT : ∀ l, (∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0) ∈ I) :
    (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) ∈ I := by
  have key : (∑ w, η w • ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) * (Q l * T l w)) -
      κ • Q (Fin.last m) = ∑ l : Fin (m + 1), ((((-1 : ℤ) ^ (m + (l : ℕ)) : ℤ) : A)) *
        (Q l * ((∑ w, η w • T l w) - algebraMap ℂ A (if l = Fin.last m then κ else 0))) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
    congr 1
    · exact Finset.sum_comm
    · rw [Finset.sum_eq_single (Fin.last m)]
      · rw [if_pos rfl, Fin.val_last, sign_last, one_mul, Algebra.smul_def, Algebra.commutes]
      · intro l _ hl
        rw [if_neg hl, map_zero, mul_zero, mul_zero]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  rw [key]
  exact Submodule.sum_mem _ fun l _ => I.mul_mem_left _ (I.mul_mem_left _ (hT l))
end Formalism.FourierDecayAlt.P.SignAntidiagonal
