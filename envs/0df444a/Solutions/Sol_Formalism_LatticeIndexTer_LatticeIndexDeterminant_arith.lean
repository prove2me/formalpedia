-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:12.410803+00:00
-- url     : https://prove2.me/submissions/c98ec97e-9dc0-488b-9f19-6d649384e7b3

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
theorem _root_.solution (x y d va vb ve ve' : ℕ∞) (h1 : ve = x + d) (h2 : ve' = y + d)
    (h3 : ve + vb = ve' + va) (hve : ve ≠ ⊤) (hve' : ve' ≠ ⊤) (hva : va ≠ ⊤) (hvb : vb ≠ ⊤) :
    (x.toNat : ℤ) - y.toNat = va.toNat - vb.toNat := by
  subst h1 h2
  have hx : x ≠ ⊤ := fun h => hve (by simp [h])
  have hd : d ≠ ⊤ := fun h => hve (by simp [h])
  have hy : y ≠ ⊤ := fun h => hve' (by simp [h])
  lift x to ℕ using hx
  lift y to ℕ using hy
  lift d to ℕ using hd
  lift va to ℕ using hva
  lift vb to ℕ using hvb
  norm_cast at h3
  simp only [ENat.toNat_natCast]
  omega
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
