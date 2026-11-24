-- Prove2me | solution 1 for DisentanglementImpossibility.orthogonal_map_std_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T21:11:43.409436+00:00
-- url     : https://prove2.me/submissions/65558cff-5c5f-49b6-8337-1ee647726697

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory
namespace DisentanglementImpossibility

theorem orthogonal_map_std_gaussian {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    (stdGaussian d).map (fun x => A.mulVec x) = stdGaussian d := by
  set G := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) with hG
  have hP : stdGaussian d = G.map (WithLp.ofLp) := by
    rw [hG, ← ProbabilityTheory.map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    have : (WithLp.ofLp ∘ WithLp.toLp 2 : (Fin d → ℝ) → (Fin d → ℝ)) = id := by
      funext x; rfl
    rw [this, Measure.map_id]
    rfl
  have hu : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A ∈
      unitary (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) hA
  set f := Unitary.linearIsometryEquiv ⟨_, hu⟩ with hf
  have hfx : ∀ x, WithLp.ofLp (f x) = A.mulVec (WithLp.ofLp x) := fun x => rfl
  have hcomp : (fun x => A.mulVec x) ∘ (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) =
      WithLp.ofLp ∘ f := by
    funext x; simp only [Function.comp_apply, hfx]
  rw [hP, Measure.map_map (by fun_prop) (by fun_prop), hcomp,
    ← Measure.map_map (by fun_prop) f.continuous.measurable, ProbabilityTheory.stdGaussian_map]

end DisentanglementImpossibility

open DisentanglementImpossibility in
theorem solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    (stdGaussian d).map (fun x => A.mulVec x) = stdGaussian d :=
  DisentanglementImpossibility.orthogonal_map_std_gaussian A hA
