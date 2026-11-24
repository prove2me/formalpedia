-- Prove2me | solution 1 for Formalism.L2.Th1.H.phase_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:44.690769+00:00
-- url     : https://prove2.me/submissions/0e324d2e-eac1-42f2-8011-44c12cb92400

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_QuadraticSemicharactersOfProductThetaMem
import Theorems.Thm_Formalism_L2_Th1_H_altE_natCast_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution (H : Sesq V) (Λ : AddSubgroup V) (hΛ : Λ ≤ dualLat H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by
  obtain ⟨m, hm⟩ := (show ∀ y ∈ Λ, ∃ m : ℤ, altE H ((N : ℂ) • s) y = (m : ℝ) from hΛ hs) x hx
  rw [altE_natCast_smul_left] at hm
  have hm' : (N : ℂ) * (altE H s x : ℂ) = (m : ℂ) := by exact_mod_cast hm
  rw [← Complex.exp_nat_mul]
  have h2 : ((2 * N : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hm'
  rw [h2, Complex.exp_int_mul_two_pi_mul_I]
end Formalism.L2.Th1.H
