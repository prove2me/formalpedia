-- Prove2me | solution 1 for DeletionCode.RuleReconstruction.recovered_rule_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:06:14.594747+00:00
-- url     : https://prove2.me/submissions/3d32cebb-6e25-4a64-93af-e95565d7deed

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
import Theorems.Thm_DeletionCode_RuleReconstruction_recovered_bubble_spectrum

set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
namespace DeletionCode.RuleReconstruction
theorem _root_.solution {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (bubbles : Finset (Fin ν)) :
    ruleSpectrum (recoveredFamily k rank (dataOfFamily E)) (windowLength k) bubbles =
      ruleSpectrum E.family (windowLength k) bubbles := by
  funext g
  unfold ruleSpectrum
  apply Finset.sum_congr rfl
  intro b hb
  exact congrFun (recovered_bubble_spectrum E rank b) g
end DeletionCode.RuleReconstruction
