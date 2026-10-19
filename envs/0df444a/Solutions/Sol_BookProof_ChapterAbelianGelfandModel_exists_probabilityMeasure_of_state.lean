-- Prove2me | solution 1 for BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:49:12.180916+00:00
-- url     : https://prove2.me/submissions/8ae62194-adff-421c-894a-beefa9ef4910

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAbelianGelfandModel

open BookProof.ChapterAbelianGelfandModel
open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder
open BookProof.ChapterLinftyMultiplication

noncomputable def h44_psi : C(Bool, ℂ) →ₗ[ℂ] ℂ where
  toFun g := 2 * g true - g false
  map_add' f g := by simp; ring
  map_smul' c f := by simp; ring

theorem solution : ¬ (∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hone : psi 1 = 1),
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧ ∀ g : C(X, ℂ), psi g = ∫ x, g x ∂mu) := by
  intro h
  obtain ⟨mu, hmu, hg⟩ := h h44_psi (by simp [h44_psi]; norm_num)
  let g : C(Bool, ℂ) := ⟨fun b => if b then 0 else 1, continuous_of_discreteTopology⟩
  have := hg g
  rw [integral_fintype (Integrable.of_finite)] at this
  simp [h44_psi, g] at this
  have h2 := congrArg Complex.re this
  simp at h2
  have : 0 ≤ mu.real {false} := measureReal_nonneg
  linarith
