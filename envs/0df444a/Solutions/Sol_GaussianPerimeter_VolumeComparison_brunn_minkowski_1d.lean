-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.brunn_minkowski_1d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:41.790065+00:00
-- url     : https://prove2.me/submissions/90831ee6-ae4b-4fa6-b8cd-d90e7c56e0a3

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_brunn_minkowski_1d_compact
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_brunn_minkowski_1d_infinite
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_biSup_add_biSup


set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {A B C : Set ℝ}
    (h : A + B ⊆ C)
    (hA_nonempty : A.Nonempty) (hA_measurable : MeasurableSet A)
    (hB_nonempty : B.Nonempty) (hB_measurable : MeasurableSet B)
    : volume A + volume B ≤ volume C := by

  -- Deal with the cases when A or B have infinite volume.
  by_cases hvolAfinite : volume A = ⊤
  · exact brunn_minkowski_1d_infinite hvolAfinite hB_nonempty h
  by_cases hvolBfinite : volume B = ⊤
  · rw [add_comm] at ⊢ h
    exact brunn_minkowski_1d_infinite hvolBfinite hA_nonempty h

  -- Use inner regularity of Lebesgue measure to reduce to the case of compact A, B
  rw [hA_measurable.measure_eq_iSup_isCompact_of_ne_top hvolAfinite,
    hB_measurable.measure_eq_iSup_isCompact_of_ne_top hvolBfinite]

  -- Want to prove:
  --   (⨆ K, ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K)
  --   + (⨆ K, ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K)
  --   ≤ volume C
  -- We'll proceed by rewriting the LHS.
  have combine_sup_conditions {A : Set ℝ} :
      (⨆ K, ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K) =
      (⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K) := by
    simp only [iSup_and]
  simp only [combine_sup_conditions]

  -- First, add in a nonempty condition:
  -- e.g. sup_{K ⊆ A} vol(K) = sup_{K ⊆ A, K nonempty} vol(K).
  have sup_vol_eq_sup_nonempty_vol {A : Set ℝ} :
      ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K =
      ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty), volume K := by
    apply le_antisymm
    · apply iSup_le; intro K
      apply iSup_le; intro hK
      by_cases h : K.Nonempty
      · apply le_iSup₂_of_le K (by simp [hK, h])
        exact le_refl (volume K)
      rw [not_nonempty_iff_eq_empty] at h
      simp [h]
    apply iSup_le; intro K
    apply iSup_le; intro hK
    apply le_iSup₂_of_le K
    · exact le_refl (volume K)
    simp [hK]
  simp only [sup_vol_eq_sup_nonempty_vol]

  -- Next, write the sum of sups as a sup of sums.
  -- sup_{K ⊆ A, K nonempty} vol(K) + sup_{L ⊆ B, L nonempty} vol(L)
  -- == sup_{K, L ⊆ A, K and L nonempty} vol(K) + vol(L).
  have combine_sups :
      (⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty), volume K)
      + (⨆ L, ⨆ (_ : L ⊆ B ∧ IsCompact L ∧ L.Nonempty), volume L)
      = ⨆ K, ⨆ L,
        ⨆ (_ : K ⊆ A ∧ IsCompact K ∧ K.Nonempty),
        ⨆ (_ : L ⊆ B ∧ IsCompact L ∧ L.Nonempty),
        volume K + volume L :=
    biSup_add_biSup
      (by use {hA_nonempty.some}; simp [hA_nonempty.some_mem])
      (by use {hB_nonempty.some}; simp [hB_nonempty.some_mem])
  rw [combine_sups]

  -- Finish using brunn_minkowski_1d_compact.
  apply iSup_le; intro K; apply iSup_le; intro L
  apply iSup_le; intro ⟨hKsubA, hKcompact, hKnonempty⟩
  apply iSup_le; intro ⟨hLsubA, hLcompact, hLnonempty⟩
  have hKplusLsubC : K + L ⊆ C := calc
    K + L ⊆ A + L := add_subset_add_right hKsubA
    _ ⊆ A + B := add_subset_add_left hLsubA
    _ ⊆ C := h
  exact brunn_minkowski_1d_compact hKplusLsubC hKnonempty hKcompact hLnonempty hLcompact
end GaussianPerimeter.VolumeComparison
