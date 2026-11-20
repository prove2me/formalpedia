-- Prove2me | solution 1 for DeletionCode.GeneratingBlocks.signedGenerating_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:54.241184+00:00
-- url     : https://prove2.me/submissions/a77bda7f-5b0d-43da-a71e-cbcc2d109563

import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_GeneratingBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingBlocks
open SignedSupport RuleSetGraph
namespace DeletionCode.GeneratingBlocks
theorem _root_.solution {B : Type*} [Fintype B] (F : RootSelection.Family B)
    (x : Windows.Letters) (n L : ℕ) :
    SignedGenerating F x n L ↔
      Generating (wordSpectrum x n L)
        (fun i : ℕ => ruleSpectrum F L (ruleBubbles F i)) id := Iff.rfl
end DeletionCode.GeneratingBlocks
