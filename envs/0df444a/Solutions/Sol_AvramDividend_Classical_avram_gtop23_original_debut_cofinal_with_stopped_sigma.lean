-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop23_original_debut_cofinal_with_stopped_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T02:51:00.200409+00:00
-- url     : https://prove2.me/submissions/337c8d07-622d-4071-947d-90af503b20c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_debut_strict_earlier_postpayment
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσruin : ∀ ω, (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℕ → ℝ)
    (hδpos : ∀ j, 0 < δ j)
    (hδlim : Tendsto δ atTop (𝓝 (0 : ℝ)))
    (S : Ω → ℝ≥0)
    (hSstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (S ω : WithTop ℝ≥0)))
    (hSle : ∀ ω, S ω ≤ σ ω)
    (hSdef : ∀ ω,
      (S ω : WithTop ℝ≥0) = ⨆ j : ℕ,
        min (σ ω : WithTop ℝ≥0)
          (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
            then (r k : WithTop ℝ≥0) else ⊤)) :
    ∀ᵐ ω ∂P, S ω = σ ω := by
  classical
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hSmeas : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | S ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using hSstop s
  have hRight :=
    avram_gclose16_original_stopping_right_neighbourhood_strict_postpayment_preruin
      X hBV x C D hD S hSmeas hSstop
  filter_upwards [hRight] with ω hright
  by_contra hne
  have hSσ : S ω < σ ω := lt_of_le_of_ne (hSle ω) hne
  have hSruin : (S ω : ℝ≥0∞) < ruinTime X x D ω :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hSσ) (hσruin ω)
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hSσ).mp (hright hSruin)
  obtain ⟨T, hST, hTu⟩ := exists_between hu.1
  have hTσ : T < σ ω := lt_of_lt_of_le hTu hu.2
  have hPrefix : ∀ s : ℝ≥0, s ≤ T →
      0 < x + X.X s ω - rightLimit D s ω := by
    intro s hsT
    by_cases hsS : s < S ω
    · obtain ⟨v, hsv, hvS⟩ := exists_between hsS
      have hvSup : (v : WithTop ℝ≥0) <
          (⨆ j : ℕ, min (σ ω : WithTop ℝ≥0)
            (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
              then (r k : WithTop ℝ≥0) else ⊤)) := by
        rw [← hSdef ω]
        exact WithTop.coe_lt_coe.mpr hvS
      exact (avram_gclose17_original_debut_strict_earlier_postpayment
        X x D hDstrat (fun η => (σ η : WithTop ℝ≥0)) hσstop r hgrid
        δ hδpos ω v hvSup) s hsv
    · exact hsub ⟨le_of_not_gt hsS, lt_of_le_of_lt hsT hTu⟩
  have hEventually :=
    avram_gclose16_original_compact_strict_sampled_exit_eventually_after_prefix
      X x D hDstrat ω T hPrefix r δ hδlim
  obtain ⟨j, hj⟩ := hEventually.exists
  have hTclock :
      (T : WithTop ℝ≥0) ≤
        min (σ ω : WithTop ℝ≥0)
          (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
            then (r k : WithTop ℝ≥0) else ⊤) :=
    le_min (WithTop.coe_le_coe.mpr (le_of_lt hTσ)) hj
  have hTS : T ≤ S ω := by
    have h : (T : WithTop ℝ≥0) ≤ (S ω : WithTop ℝ≥0) := by
      rw [hSdef ω]
      exact le_iSup_of_le j hTclock
    exact WithTop.coe_le_coe.mp h
  exact (not_le_of_gt hST) hTS
