-- Prove2me | solution 1 for Formalism.H.coeff_integrand_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:23.064029+00:00
-- url     : https://prove2.me/submissions/bb067078-d153-44a1-85a8-0da5cdb1c737

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (Λ : Submodule ℤ V) (G : V → ℂ)
    (hper : ∀ (l : Λ) (x : V), G ((l : V) + x) = G x) (μ : V) (hμ : μ ∈ dual Λ) (l : Λ) (y : V) :
    G ((l : V) + y) * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, (l : V) + y⟫ : ℝ))) =
      G y * Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) = ⟪μ, (l : V)⟫ := by
    have hm : innerₗ V μ (l : V) ∈ (1 : Submodule ℤ ℝ) := hμ (l : V) l.2
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp hm
    exact ⟨n, by simpa using hn⟩
  rw [hper l y, inner_add_right, ← hn]
  have h1 : Complex.exp (((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [← mul_one (Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ)))), ← h1, ← Complex.exp_add]
  congr 2
  push_cast
  ring
end Formalism.H
