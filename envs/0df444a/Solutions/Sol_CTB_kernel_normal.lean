-- Prove2me | solution 1 for CTB.kernel_normal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:55:23.301873+00:00
-- url     : https://prove2.me/submissions/ac642ccf-68f7-4ff1-bed3-bc6c3480e040

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

open CTB


theorem ctb84_kernel_normal {n : ℕ} {Q : Type*} [Group Q] {G : Type*} [Group G]
    (W : CrystallographicBraidWorld n Q)
    (Gam Ker : Subgroup Q) (f : Q →* G)
    (h : IsTorusBundleRealization W Gam Ker f) (_hT : TorsionFree ↥Gam) :
    ∀ g ∈ Gam, ∀ k ∈ Ker, g * k * g⁻¹ ∈ Ker := by
  obtain ⟨-, hKG, -, hKf, hGK, -⟩ := h
  intro g hg k hk
  apply hGK
  · exact Gam.mul_mem (Gam.mul_mem hg (hKG k hk)) (Gam.inv_mem hg)
  · rw [map_mul, map_mul, hKf k hk, mul_one, map_inv, mul_inv_cancel]

/-- The abelian world: `Q` is the lattice itself and the holonomy is trivial. -/
def ctb84_wA (n : ℕ) : CrystallographicBraidWorld n (Multiplicative (Fin (Nat.choose n 2) → ℤ)) where
  lattice := ⊤
  latticeNormal := inferInstance
  latticeComm := fun x _ y _ => mul_comm x y
  latticeIso := Subgroup.topEquiv
  hol := 1
  holKer := MonoidHom.ker_one
  noEvenTorsion := by
    rintro g ⟨j, hj⟩
    have h2 : ∀ i, (2 : ℤ) ^ j * (Multiplicative.toAdd g) i = 0 := by
      intro i
      have := congrFun (congrArg Multiplicative.toAdd hj) i
      simpa using this
    apply Multiplicative.toAdd.injective
    funext i
    have := h2 i
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ (by norm_num))
    · simpa using h

theorem ctb84_no_real (n : ℕ) (Gam Ker : Subgroup (Multiplicative (Fin (Nat.choose n 2) → ℤ)))
    (f : Multiplicative (Fin (Nat.choose n 2) → ℤ) →* Equiv.Perm (Fin 3)) :
    ¬ IsTorusBundleRealization (ctb84_wA n) Gam Ker f := by
  rintro ⟨-, -, -, -, -, hs⟩
  obtain ⟨x, -, hx⟩ := hs (Equiv.swap 0 1)
  obtain ⟨y, -, hy⟩ := hs (Equiv.swap 1 2)
  have h := congrArg f (mul_comm x y)
  rw [map_mul, map_mul, hx, hy] at h
  revert h; decide

theorem ctb84_preimage_false :
    ¬ (Subgroup.map (ctb84_wA 2).hol (Subgroup.comap (ctb84_wA 2).hol (⊤ : Subgroup (Equiv.Perm (Fin 2))))
      = ⊤) := by
  intro h
  have hm : Equiv.swap (0 : Fin 2) 1 ∈ Subgroup.map (ctb84_wA 2).hol
      (Subgroup.comap (ctb84_wA 2).hol (⊤ : Subgroup (Equiv.Perm (Fin 2)))) := by
    rw [h]; trivial
  obtain ⟨x, -, hx⟩ := hm
  have : (Equiv.swap (0 : Fin 2) 1) = 1 := hx.symm
  revert this; decide

theorem ctb84_sq : ∀ g : Equiv.Perm (Fin 2), g ^ 2 ^ 1 = 1 := by decide

theorem ctb84_two_torsion : ∀ g : Equiv.Perm (Fin 2), g ∈ (⊤ : Subgroup (Equiv.Perm (Fin 2))) →
    IsTwoTorsion g := fun g _ => ⟨1, ctb84_sq g⟩


/-!  Milestone 2 (Proposition 2.1 and Lemma 2.2, idealized): the kernel
of a torus-bundle realization is normal in the total-space subgroup.
If the pair of subgroups with the homomorphism f realizes the abstract
model group, and the total-space subgroup is torsion-free, then the
kernel is stable under conjugation by the elements of the total-space
subgroup, so that the quotient is a group and the realization fits into
the short exact sequence of the fibration. -/
theorem solution {n : ℕ} {Q : Type*} [Group Q] {G : Type*} [Group G]
    (W : CrystallographicBraidWorld n Q)
    (Gam Ker : Subgroup Q) (f : Q →* G)
    (h : IsTorusBundleRealization W Gam Ker f) (hT : TorsionFree ↥Gam) :
    ∀ g ∈ Gam, ∀ k ∈ Ker, g * k * g⁻¹ ∈ Ker := by
  exact ctb84_kernel_normal W Gam Ker f h hT


