-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_monotone_envelope_common_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:08:45.4479+00:00
-- url     : https://prove2.me/submissions/55f608b9-9ff3-4237-9e0a-10f7999f98a0

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem solution
    (f d : ℝ≥0 → ℝ) (hd : Monotone d) (t : ℝ≥0) (l x δ : ℝ)
    (hf : Tendsto f (𝓝[<] t) (nhds l))
    (hc : ContinuousWithinAt d (Iic t) t) :
    Tendsto (fun u => x + δ + f u - d u) (𝓝[<] t) (nhds (x + δ + l - d t)) ∧
    Tendsto (fun u => x + δ + f u - ⨅ s : Ioi u, d s)
      (𝓝[<] t) (nhds (x + δ + l - d t)) := by

  classical
  have hlt : Iio t ⊆ Iic t := by
    intro u hu
    change u ≤ t
    exact le_of_lt hu
  have hdleft : Tendsto d (𝓝[<] t) (nhds (d t)) :=
    hc.mono_left (nhdsWithin_mono t hlt)
  have hbd (u : ℝ≥0) :
      BddBelow (Set.range (fun s : Ioi u => d s)) := by
    refine ⟨d u, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hd s.property.le
  have hlow : ∀ u : ℝ≥0, d u ≤ ⨅ s : Ioi u, d s := by
    intro u
    haveI : Nonempty (Ioi u) := ⟨⟨u + 1, by simp⟩⟩
    apply le_ciInf
    intro s
    exact hd s.property.le
  have hupper : ∀ᶠ u in (𝓝[<] t), (⨅ s : Ioi u, d s) ≤ d t := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact ciInf_le (hbd u) ⟨t, hu⟩
  have hInf : Tendsto (fun u : ℝ≥0 => ⨅ s : Ioi u, d s)
      (𝓝[<] t) (nhds (d t)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hdleft tendsto_const_nhds
    · exact Filter.Eventually.of_forall hlow
    · exact hupper
  have hBase : Tendsto (fun u : ℝ≥0 => x + δ + f u)
      (𝓝[<] t) (nhds (x + δ + l)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => x + δ)
      (𝓝[<] t) (nhds (x + δ))).add hf
  exact ⟨hBase.sub hdleft, hBase.sub hInf⟩

end
