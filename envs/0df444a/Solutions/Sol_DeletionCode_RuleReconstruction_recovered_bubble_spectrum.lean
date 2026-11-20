-- Prove2me | solution 1 for DeletionCode.RuleReconstruction.recovered_bubble_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:05:29.254152+00:00
-- url     : https://prove2.me/submissions/205986c9-16d3-47f2-a009-582fce868118

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
import Theorems.Thm_DeletionCode_RuleReconstruction_recoveredFamily_agree
import Theorems.Thm_DeletionCode_RuleReconstruction_pathSpectrum_congr

set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
namespace DeletionCode.RuleReconstruction
theorem _root_.solution {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (b : Fin ν) :
    bubbleSpectrum (recoveredFamily k rank (dataOfFamily E)) (windowLength k) b =
      bubbleSpectrum E.family (windowLength k) b := by
  funext g
  unfold bubbleSpectrum
  have hn := congrFun (pathSpectrum_congr _ _ (windowLength k) (E.family.extra b false)
    (recoveredFamily_agree E rank b false)) g
  have hp := congrFun (pathSpectrum_congr _ _ (windowLength k) (E.family.extra b true)
    (recoveredFamily_agree E rank b true)) g
  exact congrArg₂ (fun a b : ℤ => a - b) hp hn
end DeletionCode.RuleReconstruction
