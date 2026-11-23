-- Prove2me | solution 1 for DensInertW.val_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:14.462924+00:00
-- url     : https://prove2.me/submissions/d586e054-166b-4c5d-ab15-ae550b6ccd71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Theorems.Thm_DensInertW_valZ_succ
import Theorems.Thm_DensInertW_valN_succ
import Theorems.Thm_DensInertW_val_recursion
import Theorems.Thm_DensInertW_finrank_valPerp
import Theorems.Thm_DensInertW_nondeg_valPerp
import Theorems.Thm_DensInertW_val_aniso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}
open Classical
namespace DensInertW
theorem _root_.solution (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M) :
    ∀ (d : ℕ) (W : Submodule L (Fin n → L)), NonDeg (Fintype.card K) M W →
      finrank L W = d → ∀ a : L, a ^ Fintype.card K = a →
        ((({v | v ∈ W ∧ hf (Fintype.card K) M v v = a} : Set (Fin n → L)).ncard : ℕ) : ℤ) =
          if a = 0 then valZ (Fintype.card K) d else valN (Fintype.card K) d := by
  intro d
  induction d with
  | zero =>
    intro W hW hd a ha
    have hW0 : W = ⊥ := by
      first
        | exact Submodule.finrank_eq_zero.mp hd
        | exact finrank_eq_zero.mp hd
    subst hW0
    have h00 : hf (Fintype.card K) M 0 0 = 0 := by
      first
        | simp [hf]
        | (unfold hf; simp [Fintype.card_ne_zero])
    by_cases ha0 : a = 0
    · subst ha0
      have hs : {v | v ∈ (⊥ : Submodule L (Fin n → L)) ∧ hf (Fintype.card K) M v v = 0} =
          ({0} : Set (Fin n → L)) := by
        ext v
        simp only [Submodule.mem_bot, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · exact fun h => h.1
        · rintro rfl
          exact ⟨rfl, h00⟩
      rw [hs, Set.ncard_singleton, if_pos rfl]
      simp [valZ]
    · have hs : {v | v ∈ (⊥ : Submodule L (Fin n → L)) ∧ hf (Fintype.card K) M v v = a} =
          (∅ : Set (Fin n → L)) := by
        ext v
        simp only [Submodule.mem_bot, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        rintro rfl
        rw [h00]
        exact fun h => ha0 h.symm
      rw [hs, Set.ncard_empty, if_neg ha0]
      simp [valN]
  | succ d ih =>
    intro W hW hd a ha
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hd
      omega
    obtain ⟨e, he, hb⟩ := val_aniso h2 hM hW hne
    have hrec := val_recursion h2 hM he hb a ha
    have hfr : finrank L (valPerp (Fintype.card K) M W e) = d := by
      have h := finrank_valPerp (q := Fintype.card K) (M := M) he hb
      omega
    have hih := ih (valPerp (Fintype.card K) M W e) (nondeg_valPerp h2 hM hW he hb) hfr a ha
    have hcardL : (Fintype.card L : ℤ) = (Fintype.card K : ℤ) ^ 2 := by
      have h := Module.card_eq_pow_finrank (K := K) (V := L)
      rw [h2] at h
      exact_mod_cast h
    rw [hfr, hcardL, hih] at hrec
    split_ifs with ha0
    · rw [if_pos ha0] at hrec
      have h := valZ_succ (Fintype.card K) d
      linarith
    · rw [if_neg ha0] at hrec
      have h := valN_succ (Fintype.card K) d
      linarith
end DensInertW
