-- Prove2me | solution 1 for FunctionalInequalities.Analysis.traceGram_posSemidef_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:43:09.333232+00:00
-- url     : https://prove2.me/submissions/92a9a270-3f95-473d-bab7-09336675fb31

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_weightedGram_408915f

noncomputable section
open scoped MatrixOrder Kronecker
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TraceGram
open scoped BigOperators Kronecker
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- The matrix indexed by derivative directions with entries `tr(B Tᵤ B Tᵥ)`
is a genuine PSD weighted Gram matrix. -/
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ a, (T a).IsSymm) :
    (Matrix.of fun a b => (B * T a * B * T b).trace).PosSemidef := by
  classical
  have hb (i j : ι) : B i j = B j i := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M j i) hB.isHermitian
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have ht (a : κ) (i j : ι) : T a j i = T a i j :=
    congrFun (congrFun (hT a) i) j
  have he (u v : κ) :
      (B * T u * B * T v).trace =
        ∑ p, ∑ q, ∑ r, ∑ s,
          B p r * B q s * T u p q * T v r s := by
    calc
      _ = ∑ r, ∑ s, ∑ q, ∑ p,
          B r p * T u p q * B q s * T v s r := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Finset.sum_mul]
      _ = ∑ r, ∑ p, ∑ q, ∑ s,
          B r p * T u p q * B q s * T v s r := by
        apply Finset.sum_congr rfl
        intro r _
        calc
          (∑ s, ∑ q, ∑ p,
              B r p * T u p q * B q s * T v s r) =
              ∑ s, ∑ p, ∑ q,
                B r p * T u p q * B q s * T v s r := by
            apply Finset.sum_congr rfl
            intro s _
            rw [Finset.sum_comm]
          _ = ∑ p, ∑ s, ∑ q,
              B r p * T u p q * B q s * T v s r := by
            rw [Finset.sum_comm]
          _ = ∑ p, ∑ q, ∑ s,
              B r p * T u p q * B q s * T v s r := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_comm]
      _ = ∑ p, ∑ q, ∑ r, ∑ s,
          B r p * T u p q * B q s * T v s r := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s _
        rw [hb r p, ht v r s]
        ring
  have hmat :
      (Matrix.of fun u v => (B * T u * B * T v).trace) =
        (Matrix.of fun u v => ∑ p, ∑ q, ∑ r, ∑ s,
          B p r * B q s * T u p q * T v r s) := by
    ext u v
    exact he u v
  rw [hmat]
  exact FunctionalInequalities.Analysis.posSemidef_weightedGram_408915f B hB T
