-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggDet_updateCol_last_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:42.09399+00:00
-- url     : https://prove2.me/submissions/24bf5ca4-8622-4d6a-aa90-ea9f8709eea7

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (n : ℕ) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_column _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · have : (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)).submatrix
        (Fin.last n).succAbove (Fin.last n).succAbove = Z.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last, updateCol_apply, (Fin.castSucc_lt_last j).ne]
    rw [this]
    simp only [updateCol_self, Pi.single_eq_same, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨n, rfl⟩, one_mul]
  · intro i _ hi
    simp [updateCol_apply, Pi.single_apply, hi]
  · simp
end Formalism.QuantumDeterminants
