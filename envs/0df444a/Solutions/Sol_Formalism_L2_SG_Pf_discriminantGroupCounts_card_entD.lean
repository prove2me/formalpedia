-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.card_entD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:36.261814+00:00
-- url     : https://prove2.me/submissions/2045755f-fba4-44c3-a660-de06f8f986c7

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution [Finite A] (d : m → A) :
    Nat.card (entD d) = ∏ i, ∏ j, Nat.card {a : A // d i * a * d j = 0} := by
  classical
  let e : (entD d) ≃ ((i : m) → (j : m) → {a : A // d i * a * d j = 0}) :=
    { toFun := fun Y i j => ⟨Y.1 i j, (show ∀ i j, d i * Y.1 i j * d j = 0 from Y.2) i j⟩
      invFun := fun f => ⟨fun i j => (f i j).1,
        (show ∀ i j, d i * (f i j).1 * d j = 0 from fun i j => (f i j).2)⟩
      left_inv := fun Y => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [Nat.card_pi]
end Formalism.L2.SG.Pf.discriminantGroupCounts
