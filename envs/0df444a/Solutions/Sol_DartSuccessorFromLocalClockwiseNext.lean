-- Prove2me | solution 1 for DartSuccessorFromLocalClockwiseNext
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:11:41.543892+00:00
-- url     : https://prove2.me/submissions/67dadc30-31ff-4e82-9a75-efbf22cc6314

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (clockwiseNext : ∀ v : V, Equiv.Perm {d : G.Dart // d.toProd.1 = v})
    (clockwiseNext_eq_self_iff_isolated :
      ∀ (v : V) (d : {d : G.Dart // d.toProd.1 = v}),
        clockwiseNext v d = d ↔ ∀ e : {d : G.Dart // d.toProd.1 = v}, e = d) :
    ∃ successor : Equiv.Perm G.Dart,
      (∀ d : G.Dart, (successor d).toProd.1 = d.toProd.2) ∧
        (∀ d : G.Dart,
          successor d =
            (clockwiseNext d.toProd.2
              ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩).1) ∧
        (∀ d : G.Dart,
          (∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e.1 = d.symm) →
            successor d = d.symm) := by
  classical
  let symmEquiv : Equiv.Perm G.Dart :=
    { toFun := fun d => d.symm
      invFun := fun d => d.symm
      left_inv := by
        intro d
        exact SimpleGraph.Dart.symm_symm d
      right_inv := by
        intro d
        exact SimpleGraph.Dart.symm_symm d }
  let tailEquiv : G.Dart ≃ Sigma (fun v : V => {d : G.Dart // d.toProd.1 = v}) :=
    { toFun := fun d => ⟨d.toProd.1, ⟨d, rfl⟩⟩
      invFun := fun s => s.2.1
      left_inv := by
        intro d
        rfl
      right_inv := by
        intro s
        cases s with
        | mk v d =>
          cases d with
          | mk d hd =>
            dsimp at hd ⊢
            cases hd
            rfl }
  let localSigmaPerm : Equiv.Perm (Sigma (fun v : V => {d : G.Dart // d.toProd.1 = v})) :=
    { toFun := fun s => ⟨s.1, clockwiseNext s.1 s.2⟩
      invFun := fun s => ⟨s.1, (clockwiseNext s.1).symm s.2⟩
      left_inv := by
        intro s
        cases s with
        | mk v d =>
          dsimp
          rw [Equiv.symm_apply_apply]
      right_inv := by
        intro s
        cases s with
        | mk v d =>
          dsimp
          rw [Equiv.apply_symm_apply] }
  let successor : Equiv.Perm G.Dart :=
    symmEquiv.trans (tailEquiv.trans (localSigmaPerm.trans tailEquiv.symm))
  refine ⟨successor, ?_, ?_, ?_⟩
  · intro d
    dsimp [successor, symmEquiv, tailEquiv, localSigmaPerm]
    exact (clockwiseNext d.toProd.2 ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩).2
  · intro d
    rfl
  · intro d hsingle
    have hnext :
        clockwiseNext d.toProd.2
            ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩ =
          ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩ := by
      exact (clockwiseNext_eq_self_iff_isolated d.toProd.2
        ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩).2 (by
          intro e
          apply Subtype.ext
          exact hsingle e)
    dsimp [successor, symmEquiv, tailEquiv, localSigmaPerm]
    exact congrArg Subtype.val hnext
