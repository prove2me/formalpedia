-- Prove2me | solution 1 for Esgk.eventually_numDistances_gt_linear_of_le_refined
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:22:00.811526+00:00
-- url     : https://prove2.me/submissions/fbc066ab-562c-415d-b45d-a102cdbfaaeb

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Theorems.Thm_Esgk_numDistances_gt_one_third_add_refined
import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_Foundation
import Definitions.Def_Esgk_Energy

section

open EuclideanGeometry Esgk
open EuclideanGeometry

theorem solution
    (A : ℝ) (hA : A ≤ 1 / 3 + 1 / 130) :
    ∀ᶠ n in Filter.atTop,
      ∀ p : Config n,
        Function.Injective p →
        InGeneralPosition (Config.toFinset p) →
        A * (n : ℝ) < (NumDistances p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 10000] with n hn
  intro p hp hgp
  have h := numDistances_gt_one_third_add_refined hp hgp hn
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end
