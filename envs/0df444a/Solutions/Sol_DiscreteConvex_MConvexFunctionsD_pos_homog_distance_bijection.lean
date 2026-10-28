-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.pos_homog_distance_bijection
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:19:37.501295+00:00
-- url     : https://prove2.me/submissions/2ab7070c-baf3-48f9-ab33-6ae6541a8973

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_GammaHat

open scoped Pointwise
open Classical

namespace DisPHD
open DiscreteConvex.MConvexFunctionsD

lemma key : GammaHat (fun (_ : Unit) (_ : Unit) => (1 : WithTop ℝ)) (fun _ => 0) ≤ 0 := by
  unfold GammaHat
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro L ⟨lam, hlam, -, rfl⟩
    simp only [Fintype.sum_unique, PosScalarMul]
    have := hlam () ()
    show ((0:ℝ) : WithTop ℝ) ≤ _
    exact_mod_cast (by simpa using this)
  · refine ⟨fun _ _ => 0, fun _ _ => le_refl _, ?_, ?_⟩
    · intro w; simp
    · simp [PosScalarMul]

end DisPHD

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (γ : V → V → WithTop ℝ),
    DiscreteConvex.MConvexFunctionsD.TriangleInequality γ →
    DiscreteConvex.MConvexFunctionsD.InducedGammaFromR (DiscreteConvex.MConvexFunctionsD.GammaHat γ) = γ ∧
    (∀ f : (V → ℝ) → WithTop ℝ, DiscreteConvex.MConvexFunctionsD.ZeroMR f →
      DiscreteConvex.MConvexFunctionsD.GammaHat (DiscreteConvex.MConvexFunctionsD.InducedGammaFromR f) = f)) := by
  intro h
  have hT : DiscreteConvex.MConvexFunctionsD.TriangleInequality
      (fun (_ : Unit) (_ : Unit) => (1 : WithTop ℝ)) := by
    intro _ _ _
    show (1 : WithTop ℝ) ≤ 1 + 1
    exact_mod_cast (by norm_num : (1:ℝ) ≤ 1 + 1)
  have h1 := congrFun (congrFun (h _ hT).1 ()) ()
  unfold DiscreteConvex.MConvexFunctionsD.InducedGammaFromR at h1
  have h2 : (fun w : Unit => ((DiscreteConvex.MConvexFunctionsD.CharVec () w : ℝ) -
      (DiscreteConvex.MConvexFunctionsD.CharVec () w : ℝ))) = fun _ => 0 := by
    funext w; simp
  have k := DisPHD.key
  simp only [h2] at h1
  rw [h1] at k
  exact absurd k (by norm_num)
