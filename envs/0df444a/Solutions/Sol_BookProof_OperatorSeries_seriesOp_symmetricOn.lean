-- Prove2me | solution 1 for BookProof.OperatorSeries.seriesOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:57:49.374527+00:00
-- url     : https://prove2.me/submissions/40af4614-8441-473b-9ca9-38e4e3294139

-- Generated from ChapterOperatorSeriesEsa.lean — solution of BookProof.OperatorSeries.seriesOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Theorems.Thm_BookProof_OperatorSeries_seriesOp_hasSum
open BookProof.OperatorSeries




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι κ : Type*} {c : ι → ℝ}
variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)
variable {T} {a}

set_option maxHeartbeats 1000000 in
theorem solution
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (hsym : ∀ k, SymmetricOn (maxDom c) (T k)) :
    SymmetricOn (maxDom c) (seriesOp T a hnorm ha) := by

  intro x y
  have h1 : HasSum (fun k => (inner ℂ (T k x : L2I ι) (y : L2I ι) : ℂ))
      (inner ℂ (seriesOp T a hnorm ha x : L2I ι) (y : L2I ι)) := by
    have h := (innerSL ℂ (y : L2I ι)).hasSum (seriesOp_hasSum hnorm ha x)
    have h2 := h.star
    simpa [inner_conj_symm] using h2
  have h2 : HasSum (fun k => (inner ℂ (x : L2I ι) (T k y : L2I ι) : ℂ))
      (inner ℂ (x : L2I ι) (seriesOp T a hnorm ha y : L2I ι)) :=
    (innerSL ℂ (x : L2I ι)).hasSum (seriesOp_hasSum hnorm ha y)
  have hEq : ∀ k, (inner ℂ (T k x : L2I ι) (y : L2I ι) : ℂ)
      = (inner ℂ (x : L2I ι) (T k y : L2I ι) : ℂ) := fun k => hsym k x y
  simp only [hEq] at h1
  exact h1.unique h2
