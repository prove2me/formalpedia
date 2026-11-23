-- Prove2me | solution 1 for Formalism.REAL.isotypicPart_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:29.979915+00:00
-- url     : https://prove2.me/submissions/6faf0ec7-b15c-4781-bd5c-0618ab753a1f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_compactSpan_le_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V)
    (hS : KStable ε F S) : isoPart ε F T S ≤ S := by
  unfold isoPart
  exact iSup₂_le fun y hy => compactSpan_le_of_mem ε F hy.1 hS
end Formalism.REAL
