-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x5.uMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:59:20.573803+00:00
-- url     : https://prove2.me/submissions/d42d2e7b-8b77-4279-8774-695b812c40fe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_herm_sum_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hzz_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_herm_f_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hermitian_form_flag_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x5
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (s : B.Mat k r)
    (U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, U c b • fvec k r z c) :
    C2.uMap k r z s = U := by
  ext a b
  unfold C2.uMap
  rw [h b]
  split_ifs with ha
  · rw [herm_sum_smul]
    simp only [herm_f_es hz.1]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; rw [if_neg (fun e => hc (Fin.ext e)), mul_zero]
    · simp
  · rw [herm_sum_smul]
    simp only [hermitian_form_flag_vector hz.1]
    rw [Finset.sum_eq_single a]
    · rw [if_pos (by have := a.isLt; omega)]
      field_simp [hzz_ne hz.2]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro e; apply hc; apply Fin.ext; have := a.isLt; omega
    · simp
end Formalism.FourierDecayAlt.P.C2x5
