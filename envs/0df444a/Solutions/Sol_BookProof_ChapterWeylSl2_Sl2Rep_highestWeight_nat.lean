-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:33.552264+00:00
-- url     : https://prove2.me/submissions/f791f569-d37f-4af1-a8a7-558c2502970c

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_H_pow_F
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_E_pow_F
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V] {R : Sl2Rep V} {w : V} {lam : ℂ}
    (hw : w ≠ 0) (hE : R.E w = 0) (h : R.H w = lam • w) :
    ∃ m : ℕ, lam = (m : ℂ) ∧ (R.F ^ (m + 1)) w = 0 := by

  classical
  have hex : ∃ k : ℕ, (R.F ^ (k + 1)) w = 0 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, (R.F ^ k) w ≠ 0 := by
      intro k
      cases k with
      | zero => simpa using hw
      | succ n => exact hcon n
    have hLI : LinearIndependent ℂ (fun k : ℕ => (R.F ^ k) w) := by
      refine Module.End.eigenvectors_linearIndependent' R.H (fun k : ℕ => lam - 2 * k) ?_ _ ?_
      · intro a b hab
        simp only [sub_right_inj] at hab
        have h2 : (a : ℂ) = b := mul_left_cancel₀ two_ne_zero hab
        exact_mod_cast h2
      · intro k
        exact ⟨Module.End.mem_eigenspace_iff.mpr (H_pow_F h k), hall k⟩
    have hfin : LinearIndependent ℂ (fun i : Fin (Module.finrank ℂ V + 1) => (R.F ^ (i : ℕ)) w) :=
      hLI.comp _ Fin.val_injective
    have hcard := hfin.fintype_card_le_finrank
    simp at hcard
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  set m := Nat.find hex with hm
  have hmne : (R.F ^ m) w ≠ 0 := by
    cases hm0 : m with
    | zero => simpa [hm0] using hw
    | succ n =>
        have := Nat.find_min hex (m := n) (by omega)
        exact this
  have key := E_pow_F hE h m
  rw [Nat.find_spec hex, map_zero] at key
  rcases smul_eq_zero.mp key.symm with hc | hc
  · have hne : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hne)
  · exact absurd hc hmne
