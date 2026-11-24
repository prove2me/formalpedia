-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas.shape_al
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:19.930715+00:00
-- url     : https://prove2.me/submissions/2bc6b75b-9546-493e-a221-3f80999fe4ba

import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeNoTrunc
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ThetaLogIsSubstitution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas
namespace Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas
theorem _root_.solution (μ : YoungDiagram) :
    (univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)).card = μ.rowLen 0 - μ.rowLen 1 := by
  have h : ∀ c : Fin (μ.rowLen 0), μ.colLen c = 1 ↔ μ.rowLen 1 ≤ c.val := by
    intro c
    have h0 : 0 < μ.colLen c :=
      YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 c.isLt)
    have h1 : (1 < μ.colLen c) ↔ c.val < μ.rowLen 1 := by
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    omega
  simp_rw [h]
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun c => if μ.rowLen 1 ≤ c then 1 else 0),
    ← Finset.card_filter]
  have : (range (μ.rowLen 0)).filter (fun c => μ.rowLen 1 ≤ c) = Ico (μ.rowLen 1) (μ.rowLen 0) := by
    ext; simp [and_comm]
  rw [this, Nat.card_Ico]
end Formalism.InvariantFactorPaths.G7.ShapeDiagramLemmas
