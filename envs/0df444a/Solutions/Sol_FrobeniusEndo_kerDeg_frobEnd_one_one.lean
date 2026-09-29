-- Prove2me | solution 1 for FrobeniusEndo.kerDeg_frobEnd_one_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/96c84609-19f0-5f5c-8031-12c9f7ec9ca4

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_kerDeg_frobEnd_one_one

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

namespace M4Wiles
namespace T2

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k]
  [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k]

omit [CommRing R] [Algebra R F] [Algebra R k] [IsScalarTower R F k] in
open Polynomial in

theorem pow_card_eq_self_iff (x : k) : x ^ Fintype.card F = x ↔ x ∈ Set.range (algebraMap F k) := by
  classical
  constructor
  · intro hx
    set q := Fintype.card F with hq
    have hq1 : 1 < q := Fintype.one_lt_card
    set f : k[X] := X ^ q - X with hf
    have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hq1

    set T : Finset k := Finset.univ.image (algebraMap F k) with hT
    have hTcard : T.card = q := by
      rw [hT, Finset.card_image_of_injective _ (algebraMap F k).injective, Finset.card_univ]
    have hTroots : T ⊆ f.roots.toFinset := by
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, ← map_pow,
        FiniteField.pow_card, sub_self]
    have hle : f.roots.toFinset.card ≤ q :=
      (Multiset.toFinset_card_le _).trans ((card_roots' f).trans_eq
        (FiniteField.X_pow_card_sub_X_natDegree_eq k hq1))
    have heq : T = f.roots.toFinset :=
      Finset.eq_of_subset_of_card_le hTroots (hle.trans_eq hTcard.symm)
    have hxroot : x ∈ f.roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hx, sub_self]
    rw [← heq, hT, Finset.mem_image] at hxroot
    obtain ⟨a, -, ha⟩ := hxroot
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

variable [DecidableEq F] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k)

omit [Fintype F] in

lemma smul_baseChange (P : (W⁄F).Point) : σ • (Point.baseChange F k P) = Point.baseChange F k P := by
  rw [algEquiv_smul_def]
  exact map_baseChange (W' := W) σ.toAlgHom P

variable {W σ}

lemma exists_baseChange_eq_of_smul_eq (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    {P : (W⁄k).Point} (hP : σ • P = P) : ∃ Q : (W⁄F).Point, Point.baseChange F k Q = P := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · have hxy : σ x = x ∧ σ y = y := by
      rw [algEquiv_smul_def, map_some] at hP
      simp only [some.injEq] at hP
      exact hP
    obtain ⟨a, ha⟩ := (pow_card_eq_self_iff x).mp (by rw [← hσ, hxy.1])
    obtain ⟨b, hb⟩ := (pow_card_eq_self_iff y).mp (by rw [← hσ, hxy.2])
    subst ha hb
    have h' : (W⁄F).Nonsingular a b :=
      (W.toAffine.baseChange_nonsingular (Algebra.ofId F k).injective (x := a) (y := b)).mp h
    exact ⟨Point.some a b h', by rw [Point.baseChange, map_some]; rfl⟩

variable (W σ)

omit [DecidableEq F] in

theorem kerDeg_one_one (hσ : ∀ x : k, σ x = x ^ Fintype.card F) :
    kerDeg (frobEnd W σ) 1 1 = Nat.card (W⁄F).Point := by
  classical
  rw [kerDeg_def]
  have hmem : ∀ P : (W⁄k).Point, P ∈ (linePencil (frobEnd W σ) 1 1).ker ↔ σ • P = P := by
    intro P
    rw [mem_ker_linePencil_iff, one_smul, one_smul, frobEnd_apply, eq_comm]
  refine Nat.card_congr (Equiv.ofBijective
    (fun Q : (W⁄F).Point => (⟨Point.baseChange F k Q, (hmem _).mpr (smul_baseChange W σ Q)⟩ :
      (linePencil (frobEnd W σ) 1 1).ker)) ⟨?_, ?_⟩).symm
  · intro Q₁ Q₂ hQ
    exact map_injective (W' := W) (Algebra.ofId F k) (congrArg Subtype.val hQ)
  · rintro ⟨P, hP⟩
    obtain ⟨Q, rfl⟩ := exists_baseChange_eq_of_smul_eq hσ ((hmem P).mp hP)
    exact ⟨Q, rfl⟩

end M4Wiles.T2

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem solution {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) : kerDeg (frobEnd W σ) 1 1 = Nat.card (W⁄F).Point :=
  M4Wiles.T2.kerDeg_one_one W σ hσ

end S_FrobeniusEndo_kerDeg_frobEnd_one_one
end P2MW
export P2MW.S_FrobeniusEndo_kerDeg_frobEnd_one_one (solution)
