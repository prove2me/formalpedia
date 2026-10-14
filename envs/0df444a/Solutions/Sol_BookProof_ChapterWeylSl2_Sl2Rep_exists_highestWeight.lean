-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:32.404642+00:00
-- url     : https://prove2.me/submissions/f3ca25dc-03db-4588-896d-28d80558760b

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_pow_succ_apply
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_H_pow_E
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
theorem solution [FiniteDimensional ℂ V] [Nontrivial V] (R : Sl2Rep V) :
    ∃ (w : V) (lam : ℂ), w ≠ 0 ∧ R.E w = 0 ∧ R.H w = lam • w := by

  classical
  obtain ⟨mu, hmu⟩ := R.H.exists_eigenvalue
  obtain ⟨v, hv, hv0⟩ := hmu.exists_hasEigenvector
  have hvH : R.H v = mu • v := Module.End.mem_eigenspace_iff.mp hv
  by_cases hall : ∀ k : ℕ, (R.E ^ k) v ≠ 0
  · exfalso
    have hLI : LinearIndependent ℂ (fun k : ℕ => (R.E ^ k) v) := by
      refine Module.End.eigenvectors_linearIndependent' R.H (fun k : ℕ => mu + 2 * k) ?_ _ ?_
      · intro a b hab
        simp only at hab
        have h1 : (2 : ℂ) * a = 2 * b := add_left_cancel hab
        have h2 : (a : ℂ) = b := mul_left_cancel₀ two_ne_zero h1
        exact_mod_cast h2
      · intro k
        exact ⟨Module.End.mem_eigenspace_iff.mpr (H_pow_E hvH k), hall k⟩
    have hfin : LinearIndependent ℂ (fun i : Fin (Module.finrank ℂ V + 1) => (R.E ^ (i : ℕ)) v) :=
      hLI.comp _ Fin.val_injective
    have hcard := hfin.fintype_card_le_finrank
    simp at hcard
  · push_neg at hall
    obtain ⟨k0, hk0⟩ := hall
    have hex : ∃ k : ℕ, (R.E ^ k) v = 0 := ⟨k0, hk0⟩
    have hpos : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Module.End.one_apply] at this
      exact hv0 this
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    refine ⟨(R.E ^ n) v, mu + 2 * n, ?_, ?_, H_pow_E hvH n⟩
    · have := Nat.find_min hex (m := n) (by omega)
      exact this
    · have := Nat.find_spec hex
      rw [hn, pow_succ_apply] at this
      exact this
