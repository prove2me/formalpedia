-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.character_estimate_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:52.810833+00:00
-- url     : https://prove2.me/submissions/23c2aab8-9a39-41e4-92b4-4b6dc33c6800

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_nonvanishing_of_hypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate
  intro ε c C hε hc hC
  obtain ⟨c', x₀, hc', h⟩ := nonvanishing_of_hypothesis ε c C hε hc hC
  refine ⟨c', x₀, hc', ?_⟩
  intro x hx y lam hy h1 h2
  constructor
  · intro N _ χ hG hb
    rw [hG, norm_neg]
    exact h x hx y lam _ hy h1 h2 hb
  · intro hG hb
    rw [hG, abs_neg]
    have h3 := h x hx y lam (fun u => ((Chebyshev.psi u - u : ℝ) : ℂ)) hy h1 h2
      (by intro u hu; simp only [Complex.norm_real, Real.norm_eq_abs]; exact hb u hu)
    have hcast : ((y : ℂ) * ∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) =
        ((y * ∫ u in Set.Ioi y, (Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ) := by
      have h4 : (∫ u in Set.Ioi y, ((Chebyshev.psi u - u : ℝ) : ℂ) / (u : ℂ) ^ 2) =
          ∫ u in Set.Ioi y, (((Chebyshev.psi u - u) / u ^ 2 : ℝ) : ℂ) := by
        congr 1
        ext u
        push_cast
        try ring
      rw [h4, Complex.ofReal_mul]
      congr 1
      first
        | exact MeasureTheory.integral_ofReal
        | exact integral_ofReal
        | exact integral_complex_ofReal
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h3
    exact h3
end Formalism.HermitianLattices.ZeroFreeRegionGL2
