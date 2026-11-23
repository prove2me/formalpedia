-- Prove2me | solution 1 for DensInertW.top_diag_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:08.511856+00:00
-- url     : https://prove2.me/submissions/78184146-42b5-44d6-bf9f-0b862dd7c504

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_DensExactInertOf
import Theorems.Thm_DensInertW_Fr_zero_zero
import Theorems.Thm_DensInertW_Fr_succ
import Theorems.Thm_DensInertW_Fr_zero_succ
import Theorems.Thm_DensInertW_top_cnt_fin_zero

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
open DensInertW
namespace DensInertW
theorem _root_.solution (hA : AnisoPeel) (hI : IsoPeel) (K L : Type) [Field K] [Fintype K]
    [Field L] [Fintype L] [Algebra K L] (h2 : Module.finrank K L = 2) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) L) (hM : IsHerm (Fintype.card K) M) :
    ∀ (m : ℕ) (w : Fin m → L) (r : ℕ), r ≤ m → (∀ i, w i ≠ 0 ↔ i.val < r) →
      (∀ i, w i ^ Fintype.card K = w i) →
      ∀ W : Submodule L (Fin n → L), NonDeg (Fintype.card K) M W →
        (cntT (Fintype.card K) M W (Matrix.diagonal w) : ℤ) =
          Fr (Fintype.card K) (Module.finrank L W) r (m - r) := by
  intro m
  induction m with
  | zero =>
    intro w r hr _ _ W _
    obtain rfl : r = 0 := by omega
    rw [top_cnt_fin_zero, Fr_zero_zero]
    rfl
  | succ c ih =>
    intro w r hr hw hwq W hW
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have hw0 : w = 0 := by
        funext i
        by_contra h
        have := (hw i).mp h
        omega
      have hdiag : Matrix.diagonal w = (0 : Matrix (Fin (c + 1)) (Fin (c + 1)) L) := by
        rw [hw0]; exact Matrix.diagonal_zero
      rw [hdiag]
      have hk := hI K L h2 n M W hM hW c (Fr (Fintype.card K) (Module.finrank L W - 2) 0 c)
        (fun W' hW' hrk => by
          have h1 := ih (fun _ => 0) 0 (Nat.zero_le _) (fun i => by simp)
            (fun i => by simp [zero_pow Fintype.card_ne_zero]) W' hW'
          rw [Matrix.diagonal_zero] at h1
          rw [h1, show Module.finrank L W' = Module.finrank L W - 2 by omega, Nat.sub_zero])
      rw [hk, Nat.sub_zero, Fr_zero_succ]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hw0 : w 0 ≠ 0 := (hw 0).mpr (by simp)
      have hcons : Matrix.diagonal w =
          Matrix.diagonal (Fin.cons (w 0) (Fin.tail w) : Fin (c + 1) → L) := by
        rw [Fin.cons_self_tail]
      rw [hcons]
      have hk := hA K L h2 n M W hM hW c (w 0) (Fin.tail w)
        (Fr (Fintype.card K) (Module.finrank L W - 1) r' (c - r')) (hwq 0) hw0
        (fun W' hW' hrk => by
          have h1 := ih (Fin.tail w) r' (by omega)
            (fun i => by simp only [Fin.tail]; rw [hw i.succ]; simp [Fin.val_succ])
            (fun i => hwq i.succ) W' hW'
          rw [h1, show Module.finrank L W' = Module.finrank L W - 1 by omega])
      rw [hk, show c + 1 - (r' + 1) = c - r' by omega, Fr_succ]
end DensInertW
