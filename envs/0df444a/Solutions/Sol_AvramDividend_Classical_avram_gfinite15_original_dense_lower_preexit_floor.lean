-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_original_dense_lower_preexit_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:08:37.991199+00:00
-- url     : https://prove2.me/submissions/ac25f2ff-ac19-4d0b-b4a8-3bccc0ba4d04

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (δ : ℝ)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤
        (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) →
      ∀ s : ℝ≥0, s < T →
        δ ≤ x + X.X s ω - rightLimit D s ω := by
  intro ω T hT s hs
  by_contra h
  have hlt : x + X.X s ω - rightLimit D s ω < δ := lt_of_not_ge h
  have hcont : ContinuousWithinAt
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω)
      (Set.Ici s) s :=
    (postPaymentReserve_cadlag_adapted X x D hD).1 ω s
  have hlocal :
      {u : ℝ≥0 | x + X.X u ω - rightLimit D u ω < δ} ∈
      𝓝[Set.Ici s] s := by
    have he : ∀ᶠ u : ℝ≥0 in 𝓝[Set.Ici s] s,
        x + X.X u ω - rightLimit D u ω ∈ Set.Iio δ :=
      hcont.eventually (isOpen_Iio.mem_nhds hlt)
    exact he
  obtain ⟨k, hk, hbelow⟩ := hgrid s T hs _ hlocal
  have hle :
      (⨅ i : ℕ, if x + X.X (r i) ω - rightLimit D (r i) ω < δ
        then (r i : WithTop ℝ≥0) else ⊤) ≤ (r k : WithTop ℝ≥0) := by
    calc
      _ ≤ (if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) := iInf_le _ k
      _ = (r k : WithTop ℝ≥0) := if_pos hbelow
  have hTk : (T : WithTop ℝ≥0) ≤ (r k : WithTop ℝ≥0) :=
    le_trans hT hle
  have hTkReal : T ≤ r k := by exact_mod_cast hTk
  exact (not_lt_of_ge hTkReal) hk
