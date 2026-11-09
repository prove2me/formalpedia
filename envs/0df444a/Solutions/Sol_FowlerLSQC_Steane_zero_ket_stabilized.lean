-- Prove2me | solution 1 for FowlerLSQC.Steane.zero_ket_stabilized
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:33:31.272179+00:00
-- url     : https://prove2.me/submissions/2dbbb3c1-059c-4ab9-9936-5772d0b8cded

import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_FowlerLSQC_Steane_bitString
import Definitions.Def_FowlerLSQC_Steane_stabilizer
import Definitions.Def_FowlerLSQC_Steane_logicalZ

namespace Aux_FowlerZ
open QAlgorithms QAlgorithms.Stabilizer

theorem keyZ (P : PauliString 7) (hph : P.phase = 0)
    (hops : ∀ q, P.ops q = .I ∨ P.ops q = .Z) :
    act P.toMatrix (ket (fun _ : Fin 7 => false)) = ket (fun _ : Fin 7 => false) := by
  have hfac : ∀ q (b : Bool), (P.ops q).mat b false = if b = false then 1 else 0 := by
    intro q b
    rcases hops q with h | h <;> rw [h] <;> cases b <;> simp [Pauli.mat, pauliZ]
  have hentry : ∀ y, P.toMatrix y (fun _ => false) = if y = (fun _ => false) then 1 else 0 := by
    intro y
    unfold PauliString.toMatrix
    rw [Matrix.of_apply, hph]
    simp only [ZMod.val_zero, pow_zero, one_mul, hfac]
    by_cases hy : y = fun _ => false
    · subst hy; simp
    · rw [if_neg hy]
      obtain ⟨q, hq⟩ : ∃ q, y q ≠ false := by
        by_contra hcon
        push_neg at hcon
        exact hy (funext hcon)
      exact Finset.prod_eq_zero (Finset.mem_univ q) (by rw [if_neg hq])
  ext y
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply, hentry]

end Aux_FowlerZ

open QAlgorithms in
open FowlerLSQC.Steane in
theorem solution :
    act logicalZ.toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) ∧
      act (stabilizer 3).toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) ∧
      act (stabilizer 4).toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) ∧
      act (stabilizer 5).toMatrix (ket (bitString ![0, 0, 0, 0, 0, 0, 0])) =
        ket (bitString ![0, 0, 0, 0, 0, 0, 0]) := by
  have hz : bitString ![0, 0, 0, 0, 0, 0, 0] = fun _ : Fin 7 => false := by
    funext q
    fin_cases q <;> rfl
  rw [hz]
  refine ⟨Aux_FowlerZ.keyZ _ rfl (by decide), Aux_FowlerZ.keyZ _ rfl (by decide),
    Aux_FowlerZ.keyZ _ rfl (by decide), Aux_FowlerZ.keyZ _ rfl (by decide)⟩
