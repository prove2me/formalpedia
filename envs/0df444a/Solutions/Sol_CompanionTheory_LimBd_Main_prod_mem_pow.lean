-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.prod_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:24:57.933835+00:00
-- url     : https://prove2.me/submissions/07219d1a-e6f1-4e23-a343-ac631a70f6b3

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_GeneratingFunctionPolynomial

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
theorem _root_.solution {ι : Type} (s : Finset ι) (q : ι → B.Mat k r → ℂ) (h : ∀ i ∈ s, q i ∈ Letters k r) :
    ∏ i ∈ s, q i ∈ Letters k r ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.mem_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end CompanionTheory.LimBd.Main
