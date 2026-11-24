-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggDet_keyN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:09.726801+00:00
-- url     : https://prove2.me/submissions/74e666cb-7b71-4005-98e0-84935423cd4a

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Theorems.Thm_Formalism_QuantumDeterminants_ggDet_updateCol_last_single

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
theorem _root_.solution (n : ℕ) (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (α β : ℂ) :
    (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W).det =
      Z.det * W.det - α * β * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det := by
  have h1 : fromBlocks Z (α • ggLastU n) (β • ggLastU n) W =
      updateCol (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W) (Sum.inr (Fin.last n))
        ((Sum.elim (0 : Fin (n + 1) → ℂ) (fun a => W a (Fin.last n))) + α • (Sum.elim (Pi.single (Fin.last n) (1 : ℂ)) (0 : Fin (n + 1) → ℂ))) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e1 : updateCol (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W) (Sum.inr (Fin.last n))
      (Sum.elim (0 : Fin (n + 1) → ℂ) (fun a => W a (Fin.last n))) = fromBlocks Z 0 (β • ggLastU n) W := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e2 : updateCol (fromBlocks Z (α • ggLastU n) (β • ggLastU n) W) (Sum.inr (Fin.last n))
      (Sum.elim (Pi.single (Fin.last n) (1 : ℂ)) (0 : Fin (n + 1) → ℂ)) =
        fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have h2 : fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0) =
      updateCol (fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0))
        (Sum.inl (Fin.last n))
        ((Sum.elim (fun a => Z a (Fin.last n)) (0 : Fin (n + 1) → ℂ)) + β • (Sum.elim (0 : Fin (n + 1) → ℂ) (Pi.single (Fin.last n) (1 : ℂ)))) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e3 : updateCol (fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0))
        (Sum.inl (Fin.last n)) (Sum.elim (fun a => Z a (Fin.last n)) (0 : Fin (n + 1) → ℂ)) =
      fromBlocks Z (ggLastU n) 0 (updateCol W (Fin.last n) 0) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e4 : updateCol (fromBlocks Z (ggLastU n) (β • ggLastU n) (updateCol W (Fin.last n) 0))
        (Sum.inl (Fin.last n)) (Sum.elim (0 : Fin (n + 1) → ℂ) (Pi.single (Fin.last n) (1 : ℂ))) =
      fromBlocks (updateCol Z (Fin.last n) 0) (ggLastU n) (ggLastU n) (updateCol W (Fin.last n) 0) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj]
  have e5 : (fromBlocks (updateCol Z (Fin.last n) 0) (ggLastU n) (ggLastU n)
        (updateCol W (Fin.last n) 0)).submatrix id
        (Equiv.swap (Sum.inl (Fin.last n)) (Sum.inr (Fin.last n))) =
      fromBlocks (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)) 0 0
        (updateCol W (Fin.last n) (Pi.single (Fin.last n) 1)) := by
    ext (i|i) (j|j) <;> by_cases hj : j = Fin.last n <;>
      simp [updateCol_apply, ggLastU, Pi.single_apply, hj, Equiv.swap_apply_def]
  have hW0 : (updateCol W (Fin.last n) 0).det = 0 :=
    det_eq_zero_of_column_eq_zero (Fin.last n) (fun i => by simp)
  have hP := det_permute' (Equiv.swap (Sum.inl (Fin.last n)) (Sum.inr (Fin.last n)))
    (fromBlocks (updateCol Z (Fin.last n) 0) (ggLastU n) (ggLastU n) (updateCol W (Fin.last n) 0))
  rw [e5, Equiv.Perm.sign_swap (by simp), det_fromBlocks_zero₂₁, ggDet_updateCol_last_single,
    ggDet_updateCol_last_single] at hP
  rw [h1, det_updateCol_add, det_updateCol_smul, e1, e2, h2, det_updateCol_add, det_updateCol_smul,
    e3, e4, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, hW0]
  push_cast at hP
  linear_combination (α * β) * hP
end Formalism.QuantumDeterminants
