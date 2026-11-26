-- Prove2me | solution 1 for Eden.hasDerivAt_euclidean_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:57.327508+00:00
-- url     : https://prove2.me/submissions/26913fe8-e081-4935-a741-0a9e950b4a17

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_Eden_Evolution

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ∀ i, HasDerivAt (fun τ => f τ i) (v i) t) : HasDerivAt f v t := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp (p := 2)).2
  intro i
  rw [ContinuousLinearMap.comp_toSpanSingleton]
  exact (hf i).hasDerivWithinAt
end Eden
