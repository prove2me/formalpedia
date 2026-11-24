-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_eq_restrict_mul_mapQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:48.13292+00:00
-- url     : https://prove2.me/submissions/4a1c275f-d501-4565-96a0-d4481da7c759

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
open Module.Basis
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {R V : Type*} [Field R] [AddCommGroup V]
    [Module R V] [Module.Finite R V] (W : Submodule R V) (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Module.Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Module.Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, this, ← LinearMap.charpoly_toMatrix _ bW,
      ← LinearMap.charpoly_toMatrix _ bQ, Matrix.charpoly_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
      simp
end Formalism.IrreducibleCountingLemmas.Z.BN
