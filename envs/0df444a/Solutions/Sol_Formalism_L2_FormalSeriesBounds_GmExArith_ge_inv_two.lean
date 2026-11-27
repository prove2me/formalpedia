-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.ge_inv_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T06:08:04.040111+00:00
-- url     : https://prove2.me/submissions/bf9bc465-15c1-45eb-9cd9-42039d47d5f1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_int_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_l
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_not_mm_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_v_eq_zero_of
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_GmExArith_ge_intCast__7e225cd13305
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution [CharZero C] (hl2 : V.l ≠ 2) : V.Ge 0 ((2 : C)⁻¹) := by
  have hcop : IsCoprime ((2 : ℕ) : ℤ) ((V.l : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Nat.prime_two V.l_prime).2 (Ne.symm hl2))
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : C) * 2 + (b : C) * (V.l : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    exact this
  have hn2 : ¬ V.MM (2 : C) := by
    intro h
    apply not_mm_one (V := V)
    rw [← h1]
    exact mm_add (mm_int_mul (ge_intCast' a) h) (mm_int_mul (ge_intCast' b) mm_l)
  have h2int : V.Ge 0 (2 : C) := by
    have := (VF.Ge.one (V := V)).add (VF.Ge.one (V := V)); rwa [one_add_one_eq_two] at this
  have hv2 : V.v (2 : C) = 0 := v_eq_zero_of h2int hn2
  have e : V.v (2 : C) + V.v (2 : C)⁻¹ = 0 := by
    rw [← V.v.map_mul, mul_inv_cancel₀ two_ne_zero, V.v.map_one]
  rw [hv2, zero_add] at e
  unfold VF.Ge; rw [e]; simp
end Formalism.L2.FormalSeriesBounds.GmExArith
