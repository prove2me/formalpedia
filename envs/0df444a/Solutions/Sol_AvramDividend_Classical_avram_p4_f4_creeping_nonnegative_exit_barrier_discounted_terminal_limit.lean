-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:15:40.597275+00:00
-- url     : https://prove2.me/submissions/2f2ed298-6606-4259-9524-749d58a4d3b0

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.SetSemiring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

/-- For lower spatial exit localisers, reserve squeezed by a shrinking
nonnegative barrier gives the exact creeping terminal limit. -/
theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q t : ℝ) (clock reserve barrier : ℕ → ℝ)
    (hclock : Tendsto clock atTop (𝓝 t))
    (hbarrier : Tendsto barrier atTop (𝓝 (0 : ℝ)))
    (hreserveNN : ∀ k, 0 ≤ reserve k)
    (hreserveLe : ∀ k, reserve k ≤ barrier k) :
    Tendsto
      (fun k => Real.exp (-(q * clock k)) * w (reserve k))
      atTop (𝓝 (Real.exp (-(q * t)) * w 0)) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have hreserve : Tendsto reserve atTop (𝓝 (0 : ℝ)) := by
    exact Filter.Tendsto.squeeze
      (f := reserve) (g := fun _ : ℕ => (0 : ℝ)) (h := barrier)
      hzero hbarrier hreserveNN hreserveLe
  have hw0 : ContinuousWithinAt w (Ici 0) 0 :=
    hw.continuousWithinAt (mem_Ici.mpr le_rfl)
  have hwithin : Tendsto reserve atTop (𝓝[Ici 0] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hreserve, Filter.Eventually.of_forall (fun k => mem_Ici.mpr (hreserveNN k))⟩
  have hvalue : Tendsto (fun k => w (reserve k)) atTop (𝓝 (w 0)) :=
    hw0.tendsto.comp hwithin
  have hexp : Tendsto (fun k => Real.exp (-(q * clock k)))
      atTop (𝓝 (Real.exp (-(q * t)))) := by
    have hcont : Continuous (fun s : ℝ => Real.exp (-(q * s))) := by
      have hlinear : Continuous (fun s : ℝ => -(q * s)) :=
        (continuous_const.mul continuous_id).neg
      exact Real.continuous_exp.comp hlinear
    exact (hcont.tendsto t).comp hclock
  exact hexp.mul hvalue
