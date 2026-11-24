-- Prove2me | solution 1 for Formalism.REAL.compactSpan_isCompactInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:46.074422+00:00
-- url     : https://prove2.me/submissions/9f4d1bad-5195-476f-9de3-54a863f15a11

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
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : KStable ε F (kSpan ε F x) := by
  intro a b hab y hy
  unfold kSpan at *
  rw [Submodule.mem_sInf] at *
  intro S hS
  exact hS.2 a b hab y (hy S hS)
end Formalism.REAL
