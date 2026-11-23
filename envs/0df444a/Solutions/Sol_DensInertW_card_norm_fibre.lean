-- Prove2me | solution 1 for DensInertW.card_norm_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:08.488114+00:00
-- url     : https://prove2.me/submissions/f41f315f-b10b-4f04-8fc3-2eb7fa39c849

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Theorems.Thm_DensInertW_card_L
import Theorems.Thm_DensInertW_one_lt_q
import Theorems.Thm_DensInertW_card_fixed
import Theorems.Thm_DensInertW_norm_fixed
import Theorems.Thm_DensInertW_card_root_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
namespace DensInertW
theorem _root_.solution [DecidableEq L] (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (haq : a ^ Fintype.card K = a) :
    #{x : L | x ^ (Fintype.card K + 1) = a} = Fintype.card K + 1 := by
  set q := Fintype.card K with hqdef
  have hq : 1 < q := one_lt_q
  set F : Finset L := {b : L | b ≠ 0 ∧ b ^ q = b} with hF
  have hFcard : F.card + 1 = q := by
    have : ({x : L | x ^ q = x} : Finset L) = insert 0 F := by
      ext b
      simp only [hF, mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro h
        by_cases hb : b = 0
        · exact Or.inl hb
        · exact Or.inr ⟨hb, h⟩
      · rintro (rfl | ⟨-, h⟩)
        · exact zero_pow (by omega)
        · exact h
    have h0 : (0 : L) ∉ F := by simp [hF]
    rw [← card_insert_of_notMem h0, ← this]
    exact card_fixed

  have hsum : ∑ b ∈ F, #{x : L | x ^ (q + 1) = b} = q ^ 2 - 1 := by
    have hmaps : ∀ x ∈ (univ.erase (0 : L)), x ^ (q + 1) ∈ F := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_mem_erase hx
      simp only [hF, mem_filter, mem_univ, true_and]
      exact ⟨pow_ne_zero _ hx0, norm_fixed h2 x⟩
    rw [← card_L h2, ← card_univ, ← card_erase_of_mem (mem_univ (0 : L)),
      card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl (fun b hb => ?_)
    have hb0 : b ≠ 0 := by simp only [hF, mem_filter, mem_univ, true_and] at hb; exact hb.1
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    constructor
    · intro h
      refine ⟨?_, h⟩
      intro hx
      subst hx
      exact hb0 (by rw [← h, zero_pow (by omega)])
    · exact fun h => h.2
  have hle : ∀ b ∈ F, #{x : L | x ^ (q + 1) = b} ≤ q + 1 := fun b _ => card_root_le q b
  have haF : a ∈ F := by simp [hF, ha0, haq]
  by_contra hne
  have hlt : #{x : L | x ^ (q + 1) = a} < q + 1 := lt_of_le_of_ne (hle a haF) hne
  have := sum_lt_sum hle ⟨a, haF, hlt⟩
  rw [hsum, sum_const, smul_eq_mul] at this
  have e : F.card = q - 1 := by omega
  rw [e] at this
  have e2 : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    have h1 : 1 ≤ q := by omega
    have h3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h3]
    ring
  omega
end DensInertW
