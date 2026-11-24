-- Prove2me | solution 1 for Formalism.H.unfoldCoeff_char_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:17.915638+00:00
-- url     : https://prove2.me/submissions/f6530443-0e94-4686-9533-13c12b1fdcd1

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (Λ : Submodule ℤ V) {μ : V} (hμ : μ ∈ dual Λ) (l : Λ) (y : V) :
    Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, (l : V) + y⟫ : ℝ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) := by
  obtain ⟨k, hk⟩ := Submodule.mem_one.1 ((LinearMap.BilinForm.mem_dualSubmodule _).1 hμ l l.2)
  have hk' : ⟪μ, (l : V)⟫ = (k : ℝ) := by simpa using hk.symm
  rw [inner_add_right, hk']
  push_cast
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + (⟪μ, y⟫ : ℂ))) =
      -(2 * (Real.pi : ℂ) * Complex.I * (⟪μ, y⟫ : ℂ)) + -(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_add, ← Int.cast_neg, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Formalism.H
