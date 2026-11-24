-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.arith3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:35:31.525088+00:00
-- url     : https://prove2.me/submissions/0a5cdd25-b3ee-408f-9e4e-d852adb31476

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution (p q p1 q1 p2 q2 p3 q3 : ℕ∞) (h : p + (q1 + q2 + q3) = q + (p1 + p2 + p3))
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : p1 ≠ ⊤) (hq1 : q1 ≠ ⊤) (hp2 : p2 ≠ ⊤) (hq2 : q2 ≠ ⊤)
    (hp3 : p3 ≠ ⊤) (hq3 : q3 ≠ ⊤) :
    (p.toNat : ℤ) - q.toNat =
      ((p1.toNat : ℤ) - q1.toNat) + ((p2.toNat : ℤ) - q2.toNat) + ((p3.toNat : ℤ) - q3.toNat) := by
  lift p to ℕ using hp
  lift q to ℕ using hq
  lift p1 to ℕ using hp1
  lift q1 to ℕ using hq1
  lift p2 to ℕ using hp2
  lift q2 to ℕ using hq2
  lift p3 to ℕ using hp3
  lift q3 to ℕ using hq3
  norm_cast at h
  simp only [ENat.toNat_natCast]
  omega
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
