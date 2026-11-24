-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.dimension_mass_joint_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:51.926037+00:00
-- url     : https://prove2.me/submissions/fc211273-bba4-46c5-a004-248bdd10de1f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : DimensionMassJointBound := by
  intro f Dstar massr Isig dsig dimV hm hI hdim h3 hD
  have hprod : ∏ ρ ∈ range f, ((2 / 3 : ℝ) * dimV ρ) ≤ ∏ ρ ∈ range f, dsig ρ := by
    apply Finset.prod_le_prod
    · intro ρ hρ
      exact mul_nonneg (by norm_num) (hdim ρ (Finset.mem_range.mp hρ))
    · intro ρ hρ
      have := h3 ρ (Finset.mem_range.mp hρ)
      linarith
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hprod
  rw [hD]
  have hmI : 0 < massr * Isig := mul_pos hm hI
  calc (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimV ρ
      = massr * Isig * ((2 / 3 : ℝ) ^ f * ∏ ρ ∈ range f, dimV ρ) := by ring
    _ ≤ massr * Isig * ∏ ρ ∈ range f, dsig ρ := mul_le_mul_of_nonneg_left hprod hmI.le
end Formalism.HermitianLattices.GlobalBoundRefinements
