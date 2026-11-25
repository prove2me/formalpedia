-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.herm_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:14:22.452826+00:00
-- url     : https://prove2.me/submissions/ee59ebd3-477c-4281-be9f-372fc1822b78

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_hpk_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate
variable {k r : ℕ}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨x, Formalism.QuantumDeterminants.Hpk k r *ᵥ y, Or.inl fun g _ => ?_⟩)
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, hpk_herm, Matrix.dotProduct_mulVec]
end CompanionTheory.LimBd.Main
