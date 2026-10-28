-- Prove2me | solution 1 for FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:14.144648+00:00
-- url     : https://prove2.me/submissions/ddadb13d-82c9-4c4e-abc8-c4f951899758

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_GradientJet

noncomputable section
open scoped RealInnerProductSpace ContDiff
section Shift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
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
