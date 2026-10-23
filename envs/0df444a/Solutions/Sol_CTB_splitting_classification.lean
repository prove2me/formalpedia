-- Prove2me | solution 1 for CTB.splitting_classification
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:56:21.894739+00:00
-- url     : https://prove2.me/submissions/a5d02ac4-3712-4624-87b0-a067bcf13978

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

theorem solution : ¬ (∀ {n : ℕ} {Q : Type} [Group Q]
    (W : CrystallographicBraidWorld n Q)
    {G1 G2 G3 G4 G5 G6 B1 B2 B3 B4 : Type}
    [Group G1] [Group G2] [Group G3] [Group G4] [Group G5] [Group G6]
    [Group B1] [Group B2] [Group B3] [Group B4],
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G1),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : G1 →* Q, (∀ y : G1, s y ∈ Gam) ∧ ∀ y : G1, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G2),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G2 →* Q, (∀ y : G2, s y ∈ Gam) ∧ ∀ y : G2, f (s y) = y) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G3),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : G3 →* Q, (∀ y : G3, s y ∈ Gam) ∧ ∀ y : G3, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G4),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G4 →* Q, (∀ y : G4, s y ∈ Gam) ∧ ∀ y : G4, f (s y) = y) ∧
    (5 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G5),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G5 →* Q, (∀ y : G5, s y ∈ Gam) ∧ ∀ y : G5, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* G6),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : G6 →* Q, (∀ y : G6, s y ∈ Gam) ∧ ∀ y : G6, f (s y) = y) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B1),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : B1 →* Q, (∀ y : B1, s y ∈ Gam) ∧ ∀ y : B1, f (s y) = y) ∧
    (3 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B2),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ∃ s : B2 →* Q, (∀ y : B2, s y ∈ Gam) ∧ ∀ y : B2, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B3),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : B3 →* Q, (∀ y : B3, s y ∈ Gam) ∧ ∀ y : B3, f (s y) = y) ∧
    (4 ≤ n → ∃ (Gam Ker : Subgroup Q) (f : Q →* B4),
        IsTorusBundleRealization W Gam Ker f ∧ TorsionFree ↥Gam ∧
        ¬∃ s : B4 →* Q, (∀ y : B4, s y ∈ Gam) ∧ ∀ y : B4, f (s y) = y)) :=
  by
  intro h
  obtain ⟨Gam, Ker, f, hr, -⟩ := (@h 3 _ _ (ctb84_wA 3) (Equiv.Perm (Fin 3)) Unit Unit Unit Unit Unit Unit Unit Unit Unit _ _ _ _ _ _ _ _ _ _).1 (by norm_num)
  exact ctb84_no_real 3 Gam Ker f hr
