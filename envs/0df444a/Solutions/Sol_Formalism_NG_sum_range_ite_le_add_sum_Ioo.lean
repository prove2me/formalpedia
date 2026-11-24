-- Prove2me | solution 1 for Formalism.NG.sum_range_ite_le_add_sum_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:41.484853+00:00
-- url     : https://prove2.me/submissions/49e3f240-4a28-49c3-8102-27201f0ea26d

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution (t : ℕ) (a : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1)) ≤ a + ∑ e ∈ Ioo 0 t, Sha e := by
  have hsub : range t ⊆ insert 0 (Ioo 0 t) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h | h
    · exact mem_insert.2 (Or.inl h)
    · exact mem_insert.2 (Or.inr (mem_Ioo.2 ⟨h, hi⟩))
  have h0 : (0 : ℕ) ∉ Ioo 0 t := by simp
  calc ∑ i ∈ range t, (if i + 1 = 1 then a else Sha (i + 1 - 1))
      ≤ ∑ i ∈ insert 0 (Ioo 0 t), (if i + 1 = 1 then a else Sha (i + 1 - 1)) :=
        sum_le_sum_of_subset hsub
    _ = a + ∑ e ∈ Ioo 0 t, Sha e := by
        rw [sum_insert h0]
        congr 1
        refine sum_congr rfl fun e he => ?_
        have hne : e + 1 ≠ 1 := by
          have := (mem_Ioo.1 he).1
          omega
        rw [if_neg hne, Nat.add_sub_cancel]
end Formalism.NG
