-- Prove2me | solution 1 for CoDecompFO.observation_A_8
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:39:37.621901+00:00
-- url     : https://prove2.me/submissions/e792bf8d-6a43-41a4-94ee-0edf0489e969

import Definitions.Def_CoDecompFO_Lim

open CoDecompFO FirstOrder in
theorem solution {σ : Sig} (T : CoDecomp σ) :
    ∃ u : T.withEq.Lim ≃[(sigmaEq σ).lang] Circ σ T.Lim,
      ∀ (x : T.withEq.Lim) (t : Fin T.b),
        CoDecomp.Lim.val (T := T) (u x) t = x.val t := by
  refine ⟨{ toFun := fun x => (⟨x.val, x.compat⟩ : T.Lim)
            invFun := fun y => (⟨y.val, y.compat⟩ : T.withEq.Lim)
            left_inv := fun x => rfl
            right_inv := fun y => rfl
            map_fun' := fun f => Empty.elim f
            map_rel' := ?_ }, fun x t => rfl⟩
  rintro n ⟨i, rfl⟩ args
  induction i using Fin.cases with
  | zero =>
    exact ⟨fun h t => congrFun (congrArg CoDecomp.Lim.val h) t,
      fun h => CoDecomp.Lim.ext (funext h)⟩
  | succ i => exact Iff.rfl
