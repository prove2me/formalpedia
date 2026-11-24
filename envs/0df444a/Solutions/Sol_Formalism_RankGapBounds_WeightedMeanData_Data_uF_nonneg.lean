-- Prove2me | solution 1 for Formalism.RankGapBounds.WeightedMeanData.Data.uF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:16.301815+00:00
-- url     : https://prove2.me/submissions/2a46a8f6-299c-46a5-8829-e62e28dc8526

import Definitions.Def_Formalism_RankGapBounds_MeanBoundSecondForm
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_le_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.WeightedMeanData
noncomputable section
open Formalism.RankGapBounds.WeightedMeanData.Data
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
namespace Formalism.RankGapBounds.WeightedMeanData.Data
theorem _root_.solution (hS : D.HidaSetting C) (u0 : U0) : 0 ≤ D.uF u0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -, hmu, -⟩ := hS
  unfold Data.uF Data.s
  have hle : ∀ u : W u0, D.muN u0 u - D.h u0 u ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) := by
    intro u
    have h1 : D.muN u0 u - D.h u0 u ≤ D.muMaxN u0 u - D.h u0 u := by linarith [hmu u0 u]
    exact h1.trans (Finset.le_sup' (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) (Finset.mem_univ u))
  have := wmean_le_const (d := D.d u0) (X := fun u => D.muN u0 u - D.h u0 u) (hd u0) _ hle
  linarith
end Formalism.RankGapBounds.WeightedMeanData.Data
