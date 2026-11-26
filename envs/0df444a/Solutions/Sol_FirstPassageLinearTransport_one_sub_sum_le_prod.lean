-- Prove2me | solution 1 for FirstPassageLinearTransport.one_sub_sum_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:28.880695+00:00
-- url     : https://prove2.me/submissions/7e72c4e9-a315-4a90-b1b1-9fca5ac096b5

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → ℚ)
    (hu : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hua := hu a (by simp)
      have hus : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ 1 := by
        intro i hi
        exact hu i (by simp [hi])
      have hsum : 0 ≤ ∑ i ∈ s, u i :=
        Finset.sum_nonneg fun i hi => (hus i hi).1
      have hfactor : 0 ≤ 1 - u a := sub_nonneg.mpr hua.2
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      calc
        1 - (u a + ∑ i ∈ s, u i) ≤
            (1 - u a) * (1 - ∑ i ∈ s, u i) := by
              nlinarith [hua.1]
        _ ≤ (1 - u a) * ∏ i ∈ s, (1 - u i) :=
          mul_le_mul_of_nonneg_left (ih hus) hfactor
end FirstPassageLinearTransport
