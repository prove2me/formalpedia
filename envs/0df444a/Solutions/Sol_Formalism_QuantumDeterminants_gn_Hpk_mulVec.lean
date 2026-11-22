-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_Hpk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:25.37251+00:00
-- url     : https://prove2.me/submissions/122d8125-b6fa-4230-97b9-4a28986ff3db

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ y) i = if _h : i.val < r ∨ r + k < i.val then y ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -y i else y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, _root_.dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [dif_pos h, Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e, one_mul]
    · intro b _ hb
      have hb' : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
      have e : Hpk k r i b = 0 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e, zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  · rw [dif_neg h, Finset.sum_eq_single i]
    · have e : Hpk k r i i = if i.val = r + k then -1 else 1 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e]
      split_ifs <;> simp
    · intro b _ hb
      have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
      have e : Hpk k r i b = 0 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e, zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
end Formalism.QuantumDeterminants
