-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:33.479959+00:00
-- url     : https://prove2.me/submissions/e3e94fa9-85a7-4e92-a0f6-782fc5ba99f7

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_lt_upper

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution (n : ℕ) : Function.Injective (@encode n) := by
  intro a b h
  have hroots (i : Fin n) : upper a i = upper b i ∧ lower a i = lower b i := by
    have hp := congrFun h (Fin.castAdd n i)
    have hm := congrFun h (Fin.natAdd n i)
    simp only [encode, Fin.append_left] at hp
    simp only [encode, Fin.append_right] at hm
    have hp' := (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp hp
    have hm' := (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp hm
    have ha := lower_lt_upper a i
    have hb := lower_lt_upper b i
    omega
  by_cases hn : 0 < n
  · have hu := (hroots ⟨0, hn⟩).1
    simp only [upper, add_zero] at hu
    have hbase : base a = base b :=
      (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : n + 1 ≠ 0)).mp hu
    funext i
    have hl := (hroots i).2
    simp only [lower, hbase] at hl
    have hK := base_ge_two b
    exact (mul_right_cancel₀ (by positivity : base b ^ (n - (i.val + 1)) ≠ 0)) hl
  · funext i
    have := i.isLt
    omega
end CSeparatedNPComplete.SquareReduction
