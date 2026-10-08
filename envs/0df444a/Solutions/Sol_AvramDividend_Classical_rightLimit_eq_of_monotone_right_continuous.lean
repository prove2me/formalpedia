-- Prove2me | solution 1 for AvramDividend.Classical.rightLimit_eq_of_monotone_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T22:29:44.324436+00:00
-- url     : https://prove2.me/submissions/81b082b7-240c-4fb7-a7f2-e956306aadf3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hmono : Monotone (fun s => D s ω))
    (hr : ContinuousWithinAt (fun s => D s ω) (Ici t) t) :
    rightLimit D t ω = D t ω := by
  have hright :
      Function.rightLim (fun s => D s ω) t = D t ω :=
    hr.rightLim_eq
  have hinf :
      Function.rightLim (fun s => D s ω) t =
        sInf ((fun s => D s ω) '' Ioi t) :=
    hmono.rightLim_eq_sInf
  change (⨅ s : Ioi t, D s.1 ω) = D t ω
  calc
    (⨅ s : Ioi t, D s.1 ω) =
        sInf ((fun s => D s ω) '' Ioi t) := by
          simp only [iInf, Set.image_eq_range]
    _ = Function.rightLim (fun s => D s ω) t := hinf.symm
    _ = D t ω := hright
