-- Prove2me | solution 1 for DeletionCode.RuleReconstruction.pathSpectrum_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:04:05.50419+00:00
-- url     : https://prove2.me/submissions/d850f8c2-750e-4348-a608-099b2e6afe81

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction

set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators
namespace DeletionCode.RuleReconstruction
theorem _root_.solution (p q : Letters) (L D : ℕ)
    (h : Agree p 0 q 0 (L + D)) : pathSpectrum p L D = pathSpectrum q L D := by
  classical
  funext g
  unfold pathSpectrum
  apply Finset.sum_congr rfl
  intro i hi
  have hgram : gram p L i.val = gram q L i.val := by
    funext j
    have hbound : i.val + j.val < L + D := by have := i.isLt; have := j.isLt; omega
    simpa only [gram, Nat.zero_add] using h (i.val + j.val) hbound
  rw [hgram]
end DeletionCode.RuleReconstruction
