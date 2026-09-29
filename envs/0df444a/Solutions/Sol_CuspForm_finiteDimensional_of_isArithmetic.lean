-- Prove2me | solution 1 for CuspForm.finiteDimensional_of_isArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ada4bc9f-6bd1-5efa-bc1b-27ad499b21b8

import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_finiteDimensional_of_isArithmetic

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

theorem solution (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by
  haveI := ModularForm.finiteDimensional_of_isArithmetic 𝒢 k
  exact Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
end

end S_CuspForm_finiteDimensional_of_isArithmetic
end P2MW
export P2MW.S_CuspForm_finiteDimensional_of_isArithmetic (solution)
