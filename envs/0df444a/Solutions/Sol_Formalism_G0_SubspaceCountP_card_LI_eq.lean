-- Prove2me | solution 1 for Formalism.G0.SubspaceCountP.card_LI_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:50.786434+00:00
-- url     : https://prove2.me/submissions/b59812e3-4a8a-4ae6-aac8-7609814011fa

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open Formalism.G0.SubspaceCountP
variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]
namespace Formalism.G0.SubspaceCountP
theorem _root_.solution (k : ℕ) :
    Nat.card (LI F W k) =
      Nat.card (Gr F W k) * ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
  classical
  let _ := Fintype.ofFinite (Gr F W k)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (F := F) (W := W) k)), Nat.card_sigma]
  have h : ∀ U : Gr F W k, Nat.card {s // spanMap k s = U} =
      ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
    intro U
    rw [Nat.card_congr (fiberEquiv k U), card_linearIndependent (by rw [U.2]), U.2]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
end Formalism.G0.SubspaceCountP
