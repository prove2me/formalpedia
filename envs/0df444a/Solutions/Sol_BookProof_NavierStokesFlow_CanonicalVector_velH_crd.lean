-- Prove2me | solution 1 for BookProof.NavierStokesFlow.CanonicalVector.velH_crd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T18:05:21.654239+00:00
-- url     : https://prove2.me/submissions/cc6b633f-e8c8-467e-94cb-1c9fc45a793b

import Mathlib
import Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_canH_eq_velH
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift.SignedHop
open BookProof.NavierStokesFlow.CanonicalVector
open scoped ENNReal
open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

namespace CFtri

theorem aFun_add (i : Fin 3) (X Y : Vel → ℂ) : aFun i (X + Y) = aFun i X + aFun i Y := by
  funext β; simp [aFun]; ring
theorem cFun_add (i : Fin 3) (X Y : Vel → ℂ) : cFun i (X + Y) = cFun i X + cFun i Y := by
  funext β; simp [cFun]; ring
theorem aFun_sub (i : Fin 3) (X Y : Vel → ℂ) : aFun i (X - Y) = aFun i X - aFun i Y := by
  funext β; simp [aFun]; ring
theorem cFun_sub (i : Fin 3) (X Y : Vel → ℂ) : cFun i (X - Y) = cFun i X - cFun i Y := by
  funext β; simp [cFun]; ring
theorem aFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) : aFun i (a • X) = a • aFun i X := by
  funext β; simp [aFun]; ring
theorem cFun_smul (i : Fin 3) (a : ℂ) (X : Vel → ℂ) : cFun i (a • X) = a • cFun i X := by
  funext β; simp [cFun]; ring

theorem lower_raise (i : Fin 3) (β : Vel) : lower i (raise i β) = β := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [lower_of_ne h, raise_of_ne h]

theorem lower_raise_comm {i k : Fin 3} (h : i ≠ k) (β : Vel) :
    lower k (raise i β) = raise i (lower k β) := by
  funext j
  by_cases hi : j = i
  · subst hi; rw [lower_of_ne h, raise_self, raise_self, lower_of_ne h]
  · by_cases hk : j = k
    · subst hk; rw [lower_self, raise_of_ne hi, raise_of_ne hi, lower_self]
    · rw [lower_of_ne hk, raise_of_ne hi, raise_of_ne hi, lower_of_ne hk]

theorem raise_comm (i k : Fin 3) (β : Vel) : raise i (raise k β) = raise k (raise i β) := by
  funext j
  by_cases hi : j = i <;> by_cases hk : j = k
  · subst hi; subst hk; rfl
  · subst hi; rw [raise_self, raise_of_ne hk, raise_of_ne hk, raise_self]
  · subst hk; rw [raise_of_ne hi, raise_self, raise_self, raise_of_ne hi]
  · rw [raise_of_ne hi, raise_of_ne hk, raise_of_ne hk, raise_of_ne hi]

theorem lower_comm (i k : Fin 3) (β : Vel) : lower i (lower k β) = lower k (lower i β) := by
  funext j
  by_cases hi : j = i <;> by_cases hk : j = k
  · subst hi; subst hk; rfl
  · subst hi; rw [lower_self, lower_of_ne hk, lower_of_ne hk, lower_self]
  · subst hk; rw [lower_of_ne hi, lower_self, lower_self, lower_of_ne hi]
  · rw [lower_of_ne hi, lower_of_ne hk, lower_of_ne hk, lower_of_ne hi]

theorem ac_same (i : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    aFun i (cFun i X) γ = cFun i (aFun i X) γ + X γ := by
  simp only [aFun, cFun, raise_self, lower_raise]
  rcases Nat.eq_zero_or_pos (γ i) with h0 | hpos
  · simp [h0]
  · have hr := CanonicalVector.raise_lower i (β := γ) hpos
    rw [hr, lower_self]
    have hc : ((γ i - 1 : ℕ) : ℝ) + 1 = (γ i : ℝ) := by
      rw [Nat.cast_sub hpos]; push_cast; ring
    rw [hc]
    have h1 : ((Real.sqrt ((γ i : ℝ) + 1) : ℂ)) * (Real.sqrt ((γ i : ℝ) + 1) : ℂ) = (γ i : ℂ) + 1 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
    have h2 : ((Real.sqrt ((γ i : ℝ)) : ℂ)) * (Real.sqrt ((γ i : ℝ)) : ℂ) = (γ i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; push_cast; ring
    push_cast
    linear_combination (X γ) * h1 - (X γ) * h2

theorem ac_ne {i k : Fin 3} (h : i ≠ k) (X : Vel → ℂ) (γ : Vel) :
    aFun i (cFun k X) γ = cFun k (aFun i X) γ := by
  simp only [aFun, cFun, raise_of_ne (Ne.symm h), lower_of_ne h, lower_raise_comm h]
  ring

theorem aa_comm (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    aFun i (aFun k X) γ = aFun k (aFun i X) γ := by
  by_cases h : i = k
  · subst h; rfl
  simp only [aFun, raise_of_ne h, raise_of_ne (Ne.symm h), raise_comm i k]
  ring

theorem cc_comm (i k : Fin 3) (X : Vel → ℂ) (γ : Vel) :
    cFun i (cFun k X) γ = cFun k (cFun i X) γ := by
  by_cases h : i = k
  · subst h; rfl
  simp only [cFun, lower_of_ne h, lower_of_ne (Ne.symm h), lower_comm i k]
  ring

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem main (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ = ladFun A c X γ := by
  simp only [canFun, ladFun, vFun, mFun, pFun, Fin.sum_univ_three, aFun_add, cFun_add,
    aFun_sub, cFun_sub, aFun_smul, cFun_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [ac_same, ac_ne (show (0:Fin 3) ≠ 1 by decide), ac_ne (show (0:Fin 3) ≠ 2 by decide),
    ac_ne (show (1:Fin 3) ≠ 0 by decide), ac_ne (show (1:Fin 3) ≠ 2 by decide),
    ac_ne (show (2:Fin 3) ≠ 0 by decide), ac_ne (show (2:Fin 3) ≠ 1 by decide),
    aa_comm 1 0 X, aa_comm 2 0 X, aa_comm 2 1 X, cc_comm 1 0 X, cc_comm 2 0 X, cc_comm 2 1 X]
  simp only [coefPair, coefRot, if_pos rfl, show ((0:Fin 3) = 1) = False by decide,
    show ((0:Fin 3) = 2) = False by decide, show ((1:Fin 3) = 0) = False by decide,
    show ((1:Fin 3) = 2) = False by decide, show ((2:Fin 3) = 0) = False by decide,
    show ((2:Fin 3) = 1) = False by decide, if_false]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  push_cast
  field_simp
  ring_nf
  rw [hs]
  ring_nf

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem crd_add (x y : lpFiniteModes Vel) : crd (x + y) = crd x + crd y := rfl
theorem crd_smul (a : ℂ) (x : lpFiniteModes Vel) : crd (a • x) = a • crd x := rfl
theorem crd_sum {ι : Type*} (s : Finset ι) (f : ι → lpFiniteModes Vel) :
    crd (∑ i ∈ s, f i) = ∑ i ∈ s, crd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, crd_add, ih]
theorem crd_ann (i : Fin 3) (x : lpFiniteModes Vel) : crd (ann i x) = aFun i (crd x) := rfl
theorem crd_cre (i : Fin 3) (x : lpFiniteModes Vel) : crd (cre i x) = cFun i (crd x) := rfl
theorem crd_pos (i : Fin 3) (x : lpFiniteModes Vel) : crd (pos i x) = pFun i (crd x) := by
  simp only [pos, LinearMap.smul_apply, LinearMap.add_apply, crd_smul, crd_add, crd_ann, crd_cre, pFun]
theorem crd_mom (i : Fin 3) (x : lpFiniteModes Vel) : crd (mom i x) = mFun i (crd x) := by
  simp only [mom, LinearMap.smul_apply, LinearMap.sub_apply, crd_smul, mFun]
  rfl
theorem lm_sum_apply {ι : Type*} (s : Finset ι) (f : ι → lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel) (x : lpFiniteModes Vel) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := LinearMap.sum_apply s f x
theorem crd_fieldV (i : Fin 3) (x : lpFiniteModes Vel) : crd (fieldV A c i x) = vFun A c i (crd x) := by
  simp only [fieldV, vFun, lm_sum_apply, LinearMap.add_apply, Finset.sum_apply,
    LinearMap.smul_apply, LinearMap.id_apply, crd_add, crd_sum, crd_smul, crd_pos]

theorem canH_crd' (x : lpFiniteModes Vel) (γ : Vel) :
    crd (canH A c x) γ = canFun A c (crd x) γ := by
  simp only [canH, canFun, lm_sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.comp_apply, crd_sum, crd_smul, crd_add, crd_mom, crd_fieldV]
  simp [Finset.sum_apply, smul_eq_mul, crd_sum, crd_add, crd_smul, crd_mom, crd_fieldV]

end CFtri

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem velH_crd' (x : lpFiniteModes Vel) (γ : Vel) :
    ((velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) :
        L2I Vel) : Vel → ℂ) γ
      = ladFun A c (crd x) γ := by
  have h := congrArg (fun T => (((T x : L2I Vel)) : Vel → ℂ) γ) (BookProof.NavierStokesFlow.CanonicalVector.canH_eq_velH A c)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  rw [← h, ← CFtri.main A c]
  exact CFtri.canH_crd' A c x γ

theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (x : lpFiniteModes Vel) (γ : Vel) :
    ((velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) :
        L2I Vel) : Vel → ℂ) γ
      = ladFun A c (crd x) γ :=
  velH_crd' A c x γ
