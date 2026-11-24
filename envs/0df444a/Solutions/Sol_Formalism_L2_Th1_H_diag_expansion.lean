-- Prove2me | solution 1 for Formalism.L2.Th1.H.diag_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:11.160392+00:00
-- url     : https://prove2.me/submissions/99cf054d-17a9-4802-bfad-265097cac253

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionFiltrationStable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_DiagonalIntegral
import Theorems.Thm_Formalism_L2_Th1_H_wt_eq_cexp


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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ)
    (Λ : AddSubgroup V) (y z : V) :
    α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)
      = ∑' x : Λ, diagCoef H α y (x : V) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) := by
  rw [wt_eq_cexp H hH z]
  simp only [opU, kerP, kerK]
  rw [← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_right]
  refine tsum_congr (fun x => ?_)
  unfold diagCoef
  have hP : (Real.pi : ℂ) * H (z + y + (x : V)) z
      + (-(Real.pi : ℂ) * H (z + y) (x : V) - Real.pi * H (x : V) (x : V) / 2)
      + (-(Real.pi : ℂ) * H z y - Real.pi * H y y / 2)
      + (-(Real.pi : ℂ) * H z z)
      = -(Real.pi : ℂ) * Complex.I * (altE H y (x : V) : ℂ)
        + (-(Real.pi : ℂ) * H (y + (x : V)) (y + (x : V)) / 2)
        + 2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ) := by
    simp only [map_add, LinearMap.add_apply, altE]
    rw [hH y z, hH (x : V) z, hH y (x : V)]
    apply Complex.ext <;> simp <;> ring
  have e1 := congrArg Complex.exp hP
  simp only [Complex.exp_add] at e1
  linear_combination (α y * α (x : V)) * e1
end Formalism.L2.Th1.H
