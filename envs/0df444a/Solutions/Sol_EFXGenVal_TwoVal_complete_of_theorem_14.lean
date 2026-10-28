-- Prove2me | solution 1 for EFXGenVal.TwoVal.complete_of_theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:53:50.762116+00:00
-- url     : https://prove2.me/submissions/b67b6b9f-6aee-404a-8350-b926c796c177

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

open EFXGenVal.TwoVal
open LittleCharity.EFX

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (hAne : A.Nonempty) (hBne : Aᶜ.Nonempty)
    (h14 : ∀ X : Fin n → Finset (Fin m), IsPartialAllocation X → (pool X).Nonempty →
      IsEFX v X → ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧
        PLexGT va vb A Y X) :
    ∃ X : Fin n → Finset (Fin m), IsPartialAllocation X ∧ pool X = ∅ ∧ IsEFX v X := by
  classical
  let S := Finset.univ.filter (fun X : Fin n → Finset (Fin m) => IsPartialAllocation X ∧ IsEFX v X)
  have hne : S.Nonempty := by
    refine ⟨fun _ => ∅, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i j _ => disjoint_bot_left, fun i j g hg => ?_⟩
    simp at hg
  obtain ⟨X, hXS, hmax⟩ := S.exists_max_image (psi va vb A) hne
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hXS
  refine ⟨X, hXS.1, ?_, hXS.2⟩
  by_contra hp
  obtain ⟨Y, hY1, hY2, hY3⟩ := h14 X hXS.1 (Finset.nonempty_iff_ne_empty.mpr hp) hXS.2
  have hle := hmax Y (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hY1, hY2⟩)
  have hlt : psi va vb A X < psi va vb A Y := hY3
  exact absurd hle (not_le.mpr hlt)
