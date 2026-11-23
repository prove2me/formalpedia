-- Prove2me | solution 1 for GenFrameSpan.det_submatrix_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:12.509264+00:00
-- url     : https://prove2.me/submissions/502904a6-e99c-4b06-8fa1-7070dbec42f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GenFrameSpan
namespace GenFrameSpan
theorem _root_.solution {R : Type*} [CommRing R] {p n : ℕ} (M : Matrix (Fin p) (Fin n) R)
    (f : Fin p → Fin n) :
    (M.submatrix id f).det = 0 ∨ ∃ (J : Fin p ↪o Fin n) (e : ℤ),
      (M.submatrix id f).det = (e : R) * (M.submatrix id J).det := by
  classical
  by_cases hf : Function.Injective f
  · right
    set s := Finset.univ.image f with hs
    have hcard : s.card = p := by
      rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    let J := s.orderEmbOfFin hcard
    have hmem : ∀ i, f i ∈ Set.range J := by
      intro i
      rw [Finset.range_orderEmbOfFin]
      simp [hs]
    choose g hg using hmem
    have hginj : Function.Injective g := by
      intro a b h
      apply hf
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin p) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)
    refine ⟨J, (Equiv.Perm.sign σ : ℤ), ?_⟩
    have e : M.submatrix id f = (M.submatrix id J).submatrix id σ := by
      ext a b
      simp [σ, hg]
    rw [e, Matrix.det_permute']
    try norm_cast
  · left
    rw [Function.Injective] at hf
    push_neg at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hij])
end GenFrameSpan
