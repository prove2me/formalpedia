-- Prove2me | solution 1 for AvramDividend.Classical.deriv_tendsto_atTop_of_derivZeroPlus_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:25:33.389202+00:00
-- url     : https://prove2.me/submissions/fac6bd62-36ca-45b2-8f70-b5ca6b4a270f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (h : derivZeroPlus W = ⊤) :
    Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop := by
  apply tendsto_atTop.2
  intro b
  have hb : (b : EReal) < derivZeroPlus W := by
    rw [h]
    simp
  have hu : (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≥ ·)
      (fun x => ((deriv W x : ℝ) : EReal)) :=
    ⟨(⊥ : EReal), Filter.Eventually.of_forall (fun x => bot_le)⟩
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      (b : EReal) < ((deriv W x : ℝ) : EReal) :=
    Filter.eventually_lt_of_lt_liminf (by
      simpa only [derivZeroPlus] using hb) hu
  filter_upwards [hev] with x hx
  have hr : b < deriv W x := by
    exact_mod_cast hx
  exact hr.le
