-- Prove2me | solution 1 for Formalism.REAL.compactSpan_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.277803+00:00
-- url     : https://prove2.me/submissions/58200e4a-8ed5-40dc-9430-e08f8eeb78de

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf

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
    (F : Fin n → Fin n → Module.End ℂ V) {x : V} {S : Submodule ℂ V} (hx : x ∈ S)
    (hS : KStable ε F S) : kSpan ε F x ≤ S :=
  sInf_le ⟨hx, hS⟩
end Formalism.REAL
