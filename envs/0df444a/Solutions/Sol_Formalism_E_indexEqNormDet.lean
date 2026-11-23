-- Prove2me | solution 1 for Formalism.E.indexEqNormDet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:25.719142+00:00
-- url     : https://prove2.me/submissions/65d4275d-cf93-4a9c-93cc-a35584030b5b

import Definitions.Def_Formalism_FockGram_StatementLat
import Definitions.Def_Formalism_FockGram_FockGramProofs_SubIndexNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open Formalism Formalism.E
namespace Formalism.E
theorem _root_.solution : SubIndexNorm := by
  intro S M ι _ _ _ _ _ _ _ b N bN
  classical
  haveI : Module.Free S M := Module.Free.of_basis b
  haveI : Module.Finite S M := Module.Finite.of_basis b
  haveI : Module.Free ℤ M := Module.Free.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  haveI : Module.Finite ℤ M := Module.Finite.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  let e0 : M ≃ₗ[S] N := b.equiv bN (Equiv.refl ι)
  let f : M →ₗ[S] M := N.subtype ∘ₗ e0.toLinearMap
  have hS : b.det (fun i => (bN i : M)) = LinearMap.det f := by
    rw [Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext x y
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [f, e0]
  let N' : Submodule ℤ M := N.restrictScalars ℤ
  let e : M ≃ₗ[ℤ] N' := (e0.trans (Submodule.restrictScalarsEquiv ℤ S M N).symm).restrictScalars ℤ
  have h1 := Submodule.natAbs_det_equiv N' e
  have hcard : Nat.card (M ⧸ N') = Nat.card (M ⧸ N) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv
  rw [← hcard, ← h1, hS, ← LinearMap.det_restrictScalars]
  congr 2
end Formalism.E
