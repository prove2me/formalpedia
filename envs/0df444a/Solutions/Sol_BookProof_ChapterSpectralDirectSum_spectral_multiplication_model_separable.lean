-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:05:12.71297+00:00
-- url     : https://prove2.me/submissions/af04d249-766c-4d3d-acfa-99dbdb91b4b3

import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum

open BookProof.ChapterSpectralDirectSum
open MeasureTheory Complex
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

theorem h44_spec_nil {A : Type*} [Ring A] [Algebra ℂ A] {N : A} (hN : IsNilpotent N) (z : ℂ)
    (hz : z ∈ spectrum ℂ N) : z = 0 := by
  by_contra h
  apply hz
  have hu : IsUnit (algebraMap ℂ A z) := (IsUnit.mk0 z h).map (algebraMap ℂ A)
  have := (hN.neg).isUnit_add_left_of_commute hu ((Algebra.commutes z (-N)).symm)
  rw [spectrum.mem_resolventSet_iff]
  simpa [sub_eq_add_neg] using this

theorem h44_zero_of_hilbertSum {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
    {V : ∀ i, G i →ₗᵢ[ℂ] E} (hV : IsHilbertSum ℂ G V) (T : E →L[ℂ] E)
    (h : ∀ i (u : G i), T (V i u) = 0) : T = 0 := by
  ext x
  obtain ⟨f, rfl⟩ := hV.surjective_isometry x
  have hs := hV.OrthogonalFamily.hasSum_linearIsometry f
  have := (hs.map T T.continuous)
  simp only [Function.comp_def, h] at this
  simpa using this.unique hasSum_zero

theorem h44_nil : IsNilpotent (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; 0, 0]) := by
  refine ⟨2, ?_⟩
  rw [← map_pow]
  have : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, map_zero]

theorem h44_ne : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; 0, 0] ≠ 0 := by
  intro h0
  rw [← map_zero (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))] at h0
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).injective h0
  have := congrFun (congrFun h 0) 1
  simp at this

theorem solution : ¬ (∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) [TopologicalSpace.SeparableSpace H],
    ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T))
      (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      S.Countable ∧
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) (coordFn T) u) = T (V x u))) := by
  intro h
  obtain ⟨S, mu, V, -, -, hV, hint⟩ := h (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; 0, 0])
  have hc : coordFn (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 1; 0, 0]) = 0 := by
    ext z
    exact h44_spec_nil h44_nil z.1 z.2
  apply h44_ne
  refine h44_zero_of_hilbertSum hV _ fun x u => ?_
  rw [← hint, hc, mulRep_zero]
  simp
