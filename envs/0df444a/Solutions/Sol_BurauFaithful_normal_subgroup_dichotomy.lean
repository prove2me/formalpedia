-- Prove2me | solution 1 for BurauFaithful.normal_subgroup_dichotomy
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T21:23:22.185403+00:00
-- url     : https://prove2.me/submissions/e0a62be3-538b-4a64-b388-4a4aa7a7bbd1

import Mathlib
import Definitions.Def_BurauFaithful_UnreducedBurau
set_option autoImplicit false

namespace CexCda1a80c

open BraidsLinksMCG

/-- Generic: a map on `Fin 2` satisfying the braid relation descends to `ArtinBraidGroup 3`. -/
def liftB3 {G : Type} [Group G] (f : Fin (3 - 1) → G)
    (hf : f 0 * f 1 * f 0 = f 1 * f 0 * f 1) : ArtinBraidGroup 3 →* G :=
  PresentedGroup.toGroup (rels := braidRels 3) (f := f) (by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exfalso
      have hi := i.isLt; have hj := j.isLt
      have : ((i : ℤ) - (j : ℤ)).natAbs ≤ 1 := by
        simp only [show 3 - 1 = 2 from rfl] at hi hj
        omega
      omega
    · have hi := i.isLt; have hj := j.isLt
      have hi0 : i = 0 := Fin.ext (by simp only [show 3 - 1 = 2 from rfl] at hi hj; simp; omega)
      have hj1 : j = 1 := Fin.ext (by simp only [show 3 - 1 = 2 from rfl] at hi hj; simp; omega)
      subst hi0 hj1
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hf, mul_inv_cancel])

theorem liftB3_sigma {G : Type} [Group G] (f : Fin (3 - 1) → G)
    (hf : f 0 * f 1 * f 0 = f 1 * f 0 * f 1) (i : Fin (3 - 1)) :
    liftB3 f hf (sigma i) = f i :=
  PresentedGroup.toGroup.of _

def fS : Fin (3 - 1) → Equiv.Perm (Fin 3) := ![Equiv.swap 0 1, Equiv.swap 1 2]
theorem fS_rel : fS 0 * fS 1 * fS 0 = fS 1 * fS 0 * fS 1 := by decide

def fA : Fin (3 - 1) → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.swap 0 1 * Equiv.swap 1 3]
theorem fA_rel : fA 0 * fA 1 * fA 0 = fA 1 * fA 0 * fA 1 := by decide

def φ : ArtinBraidGroup 3 →* Equiv.Perm (Fin 3) := liftB3 fS fS_rel
def ψ : ArtinBraidGroup 3 →* Equiv.Perm (Fin 4) := liftB3 fA fA_rel

theorem cex : ¬ (∀ (n : ℕ) (K : Subgroup (ArtinBraidGroup n)) [K.Normal],
    K ≤ Subgroup.center (ArtinBraidGroup n) ∨
      commutator (ArtinBraidGroup n) ≤ K) := by
  intro h
  rcases h 3 φ.ker with hc | hk
  · have hmem : sigma (0 : Fin (3 - 1)) * sigma 0 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, φ, liftB3_sigma]
      decide
    have hz := Subgroup.mem_center_iff.mp (hc hmem) (sigma (1 : Fin (3 - 1)))
    have := congrArg ψ hz
    simp only [map_mul, ψ, liftB3_sigma] at this
    revert this
    decide
  · have hmem := hk (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (sigma (n := 3) 0)) (Subgroup.mem_top (sigma (n := 3) 1)))
    rw [MonoidHom.mem_ker, commutatorElement_def] at hmem
    simp only [map_mul, map_inv, φ, liftB3_sigma] at hmem
    revert hmem
    decide

end CexCda1a80c

theorem solution : ¬ (∀ (n : ℕ) (K : Subgroup (BraidsLinksMCG.ArtinBraidGroup n)) [K.Normal],
    K ≤ Subgroup.center (BraidsLinksMCG.ArtinBraidGroup n) ∨
      commutator (BraidsLinksMCG.ArtinBraidGroup n) ≤ K) := by
  exact CexCda1a80c.cex
