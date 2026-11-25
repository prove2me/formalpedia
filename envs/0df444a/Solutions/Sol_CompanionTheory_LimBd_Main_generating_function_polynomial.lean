-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.generating_function_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:31:00.79618+00:00
-- url     : https://prove2.me/submissions/945a99e5-fd6b-4a2a-b7ea-6e54074dc7db

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial
import Theorems.Thm_CompanionTheory_LimBd_Main_dmin_mem

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
theorem _root_.solution : GfPoly := by
  intro k r z z' p
  have h : (fun g : B.Mat k r => ((Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by
    have := Submodule.sub_mem _ (dmin_mem z z' (Fin.last (r + 1)))
      (Submodule.smul_mem _ ((Formalism.QuantumDeterminants.Tz k r z * Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) (dmin_mem z z' ⟨r, by omega⟩))
    convert this using 1
    funext g
    simp [Formalism.QuantumDeterminants.Gf]
  rw [pow_mul]
  convert Submodule.pow_mem_pow _ h p using 1
  funext g
  simp
end CompanionTheory.LimBd.Main
