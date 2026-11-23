-- Prove2me | solution 1 for Formalism.L2.Th1.H.norm_diagCoef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:50.358137+00:00
-- url     : https://prove2.me/submissions/1dba80e3-659a-4492-9ac8-64ce796c9683

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionFiltrationStable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_DiagonalIntegral

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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (y x : V)
    (hy : α y = 1 ∨ α y = -1) (hx : α x = 1 ∨ α x = -1) :
    ‖diagCoef H α y x‖ = Real.exp (-(Real.pi / 2) * (H (y + x) (y + x)).re) := by
  have hn : ∀ a : ℂ, (a = 1 ∨ a = -1) → ‖a‖ = 1 := by
    rintro a (rfl | rfl) <;> simp
  unfold diagCoef
  rw [norm_mul, norm_mul, norm_mul, hn _ hy, hn _ hx, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(Real.pi : ℂ) * Complex.I * (altE H y x : ℂ)).re = 0 := by
    simp
  have h2 : (-(Real.pi : ℂ) * H (y + x) (y + x) / 2).re = -(Real.pi / 2) * (H (y + x) (y + x)).re := by
    simp
    ring
  rw [h1, h2]
  simp
end Formalism.L2.Th1.H
