-- Prove2me | solution 1 for Formalism.NG.sum_ite_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:40.525594+00:00
-- url     : https://prove2.me/submissions/dfbdf164-025c-4cfd-92aa-079b00e55c80

import Definitions.Def_Formalism_CharacterColumnKernels_StatementNG
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SumIteLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution (t : ℕ) (vhE : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then vhE else Sha (i + 1 - 1)) ≤
      vhE + ∑ e ∈ Ioo 0 t, Sha e := by
  rcases t with _ | n
  · simp
  · have hs : Ioo 0 (n + 1) = (range n).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext e
      simp only [mem_Ioo, mem_map, mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h
        exact ⟨e - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [hs, Finset.sum_map, Finset.sum_range_succ', add_comm]
    refine add_le_add (le_of_eq (if_pos rfl)) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    show (if i + 1 + 1 = 1 then vhE else Sha (i + 1 + 1 - 1)) = Sha (i + 1)
    exact (if_neg (by omega)).trans (congrArg Sha (by omega))
end Formalism.NG
