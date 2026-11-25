-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.lattice_inclusion_forms_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:17.293686+00:00
-- url     : https://prove2.me/submissions/e8a80791-07ff-4e13-aeb0-dc059acdf1e8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Cart
variable (X : Cart V d I J)
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}
end Cart
namespace Sys
variable {X : Cart V d I J} (S : Sys X)
end Sys
private theorem ge_zero_l_pow_mul_of_mem_Ty (X : Cart V d I J) :
    ∀ (i : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → ∀ n, V.Ge 0 ((V.l : C) ^ i * x i n) := by
  intro i
  induction i with
  | zero =>
    intro x hx n
    rw [pow_zero, one_mul]
    exact X.t2 x hx 0 (fun j hj => absurd hj (Nat.not_lt_zero _)) n
  | succ i ih =>
    intro x hx n
    have h := ih (Fs V.l x) (X.F_mem x hx) n
    simp only [Fs] at h
    rw [pow_succ, mul_assoc]
    exact h
private theorem ge_neg_of_ge_zero_l_pow_mul (i : ℕ) (y : C) (h : V.Ge 0 ((V.l : C) ^ i * y)) : V.Ge (-(i : ℝ)) y := by
  unfold VF.Ge at *
  rw [AddValuation.map_mul, AddValuation.map_pow, V.v_l] at h
  have hi : (i • (1 : WithTop ℝ)) = ((i : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
  rw [hi] at h
  by_cases hy : V.v y = ⊤
  · rw [hy]
    exact le_top
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← ht] at h ⊢
    rw [← WithTop.coe_add] at h
    have h' := WithTop.coe_le_coe.mp h
    exact WithTop.coe_le_coe.mpr (by linarith)
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (X : Cart V d I J) : LatticeInclusionFormsInjective X := by
  intro S c i n
  exact ge_neg_of_ge_zero_l_pow_mul i _ (ge_zero_l_pow_mul_of_mem_Ty X i _ (S.mem c) n)
end Formalism.L2.FormalSeriesBounds
