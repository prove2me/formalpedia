-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.card_ker_mulDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:18:37.120802+00:00
-- url     : https://prove2.me/submissions/d7b41dec-ad62-46bb-90e9-1a18df312449

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
    Nat.card (AddMonoidHom.mulRight (diagonal d)).ker =
      ∏ _i : m, ∏ j : m, Nat.card {a : A // a * d j = 0} := by
  classical
  let e : (AddMonoidHom.mulRight (diagonal d)).ker ≃ ((i : m) → (j : m) → {a : A // a * d j = 0}) :=
    { toFun := fun Y i j => ⟨Y.1 i j, by
        have h : Y.1 * diagonal d = 0 := Y.2
        have h' := congrFun (congrFun h i) j
        rwa [Matrix.mul_diagonal, Matrix.zero_apply] at h'⟩
      invFun := fun f => ⟨Matrix.of fun i j => (f i j).1, by
        show Matrix.of (fun i j => (f i j).1) * diagonal d = 0
        ext i j
        simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply]
        exact (f i j).2⟩
      left_inv := fun Y => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [Nat.card_pi]
end Formalism.L2.SG.Pf.discriminantGroupCounts
