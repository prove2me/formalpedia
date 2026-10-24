-- Prove2me | solution 1 for FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:43:21.988321+00:00
-- url     : https://prove2.me/submissions/ab3e0cd7-a4d6-41a4-bb96-95ff8f29c6d7

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section Shift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Shift invariance of higher iterated derivatives**: for `r ≥ 1`,
`Dʳ(f − c)(x) = Dʳf(x)`. -/
theorem solution {f : E → F} (hf : ContDiff ℝ ∞ f) (c : F) {r : ℕ} (hr : 1 ≤ r)
    (x : E) : iteratedFDeriv ℝ r (fun z => f z - c) x = iteratedFDeriv ℝ r f x := by
    have hf' : ContDiff ℝ r f :=
      hf.of_le (WithTop.coe_le_coe.mpr (le_top : r ≤ (⊤ : ℕ∞)))
    have hc' : ContDiff ℝ r (fun _ : E => c) := contDiff_const
    calc
      iteratedFDeriv ℝ r (fun z => f z - c) x =
          iteratedFDeriv ℝ r f x -
            iteratedFDeriv ℝ r (fun _ : E => c) x := by
        exact
          (iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := r) (f := f)
            (g := fun _ : E => c) hf'.contDiffAt hc'.contDiffAt)
      _ = iteratedFDeriv ℝ r f x := by
        rw [iteratedFDeriv_const_of_ne (by omega : r ≠ 0) c]
        simp
