-- Prove2me | solution 1 for AvramDividend.Classical.admissibleLe_rightLimit_zero_ge_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:48:59.27399+00:00
-- url     : https://prove2.me/submissions/41767ecc-daef-4eea-aa89-4edb94e2b23f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c) (hcx : c < x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    ∀ ω, x - c ≤ rightLimit D 0 ω := by
  rcases hD with ⟨⟨hstrat, hjump⟩, hcap⟩
  rcases hstrat with ⟨hD0, hmono, hleft, hadapt⟩
  intro ω
  simp only [rightLimit]
  refine le_ciInf (fun s => ?_)
  have hXlim :
      Tendsto (fun t : ℝ≥0 => X.X t ω) (𝓝[>] 0) (𝓝 (X.X 0 ω)) :=
    (X.rightCont ω 0).mono Ioi_subset_Ici_self
  have hlim :
      Tendsto (fun t : ℝ≥0 => x + X.X t ω - c)
        (𝓝[>] 0) (𝓝 (x - c)) := by
    convert (tendsto_const_nhds.add hXlim).sub_const c using 1 <;>
      simp [X.X_zero ω]
  refine le_of_tendsto hlim ?_
  filter_upwards [
    self_mem_nhdsWithin,
    (eventually_lt_nhds s.2).filter_mono nhdsWithin_le_nhds
  ] with t ht hts
  have hcap_t : riskProcess X x D t ω ≤ c := by
    exact (ENNReal.ofReal_le_ofReal_iff hc).1 (hcap ω t ht)
  have hmono_ts := hmono ω hts.le
  simp only [riskProcess] at hcap_t
  linarith
