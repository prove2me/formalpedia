-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop20_original_lower_exit_cofinal_floor_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T03:21:30.292608+00:00
-- url     : https://prove2.me/submissions/379b4c69-c6ca-4ff9-8f07-2c9c4b82caab

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_lower_exit_clocks_antitone_barriers
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_lower_exit_debut_sup_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gtop23_original_debut_cofinal_with_stopped_sigma
import Theorems.Thm_AvramDividend_Classical_avram_gtop24_bounded_withtop_stop_has_nnreal_rep
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσle : ∀ ω, σ ω ≤ τ ω) :
    ∃ L : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (L j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, L j ω ≤ σ ω) ∧
      (∀ ω, Monotone (fun j : ℕ => L j ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => L j ω) atTop (nhds (σ ω))) ∧
      (∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < L j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) := by
  classical
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  let r : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  have hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U := by
    intro s t hst U hU
    obtain ⟨u, hu, hsub⟩ :=
      (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hst).mp hU
    obtain ⟨v, hsv, hvu⟩ := exists_between hu.1
    obtain ⟨k, hk⟩ := (TopologicalSpace.denseRange_denseSeq ℝ≥0).exists_mem_open
      isOpen_Ioo (⟨v, ⟨hsv, hvu⟩⟩ : (Set.Ioo s u).Nonempty)
    exact ⟨k, lt_of_lt_of_le hk.2 hu.2, hsub ⟨le_of_lt hk.1, hk.2⟩⟩
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδpos : ∀ j, 0 < δ j := by intro j; dsimp [δ]; positivity
  have hδanti : Antitone δ := by
    intro j k hjk
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hδlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 (0 : ℝ))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let R : ℕ → Ω → WithTop ℝ≥0 := fun j ω =>
    min (σ ω : WithTop ℝ≥0)
      (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
        then (r k : WithTop ℝ≥0) else ⊤)
  have hRstop : ∀ j, IsStoppingTime 𝓕.rightCont (R j) := by
    intro j
    exact (avram_gclose16_original_sampled_preexit_clipped_clock_floor
      X x D hDstrat (fun ω => (σ ω : WithTop ℝ≥0)) hσstop r hgrid (δ j)).1
  have hRle : ∀ j ω, R j ω ≤ (σ ω : WithTop ℝ≥0) := by
    intro j
    exact (avram_gclose16_original_sampled_preexit_clipped_clock_floor
      X x D hDstrat (fun ω => (σ ω : WithTop ℝ≥0)) hσstop r hgrid (δ j)).2.1
  have hRmono : ∀ ω, Monotone (fun j => R j ω) := by
    simpa only [R] using
      (avram_gclose17_original_lower_exit_clocks_antitone_barriers
        X x D (fun ω => (σ ω : WithTop ℝ≥0)) r δ hδanti)
  obtain ⟨hSupStop, hSupLe⟩ :=
    avram_gclose17_original_lower_exit_debut_sup_stopping
      X x D hDstrat (fun ω => (σ ω : WithTop ℝ≥0)) hσstop r hgrid δ
  obtain ⟨S, hScoe, hSstop, hSle⟩ :=
    avram_gtop24_bounded_withtop_stop_has_nnreal_rep 𝓕 σ
      (fun ω => ⨆ j, R j ω) hSupStop hSupLe
  have hσruin : ∀ ω, (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro ω
    calc
      (σ ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (hσle ω)
      _ ≤ ruinTime X x D ω := by
        rw [hτeq ω]
        exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.2 ω
  have hSdef : ∀ ω, (S ω : WithTop ℝ≥0) =
      ⨆ j, min (σ ω : WithTop ℝ≥0)
        (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
          then (r k : WithTop ℝ≥0) else ⊤) := hScoe
  have hScof : ∀ᵐ ω ∂P, S ω = σ ω :=
    avram_gtop23_original_debut_cofinal_with_stopped_sigma
      X hBV x C D hD σ hσstop hσruin r hgrid δ hδpos hδlim
      S hSstop hSle hSdef
  have hEach : ∀ j, ∃ Lj : Ω → ℝ≥0,
      (∀ ω, (Lj ω : WithTop ℝ≥0) = R j ω) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (Lj ω : WithTop ℝ≥0)) ∧
      ∀ ω, Lj ω ≤ σ ω := by
    intro j
    exact avram_gtop24_bounded_withtop_stop_has_nnreal_rep 𝓕 σ
      (R j) (hRstop j) (hRle j)
  choose L hLcoe hLstop hLle using hEach
  have hLmono : ∀ ω, Monotone (fun j : ℕ => L j ω) := by
    intro ω j k hjk
    apply WithTop.coe_le_coe.mp
    rw [hLcoe j ω, hLcoe k ω]
    exact hRmono ω hjk
  have hLlimit : ∀ᵐ ω ∂P,
      Tendsto (fun j => L j ω) atTop (nhds (σ ω)) := by
    filter_upwards [hScof] with ω hω
    have hbdd : BddAbove (Set.range (fun j => L j ω)) := by
      refine ⟨σ ω, ?_⟩
      rintro z ⟨j, rfl⟩
      exact hLle j ω
    let u : ℝ≥0 := sSup (Set.range (fun j => L j ω))
    have hu : u = σ ω := by
      apply le_antisymm
      · apply csSup_le (Set.range_nonempty _)
        rintro z ⟨j, rfl⟩
        exact hLle j ω
      · apply WithTop.coe_le_coe.mp
        calc
          (σ ω : WithTop ℝ≥0) = (S ω : WithTop ℝ≥0) :=
            congrArg (fun a : ℝ≥0 => (a : WithTop ℝ≥0)) hω.symm
          _ = ⨆ j, R j ω := hScoe ω
          _ ≤ (u : WithTop ℝ≥0) := by
            apply iSup_le
            intro j
            rw [← hLcoe j ω]
            exact WithTop.coe_le_coe.mpr
              (le_csSup hbdd (Set.mem_range_self j))
    have htend : Tendsto (fun j => L j ω) atTop (nhds u) := by
      exact tendsto_atTop_ciSup (hLmono ω) hbdd
    simpa only [hu] using htend
  have hFloor : ∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < L j ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω := by
    intro j
    filter_upwards [] with ω t ht0 ht
    have hc : (L j ω : WithTop ℝ≥0) ≤ R j ω := (hLcoe j ω).le
    have hz := (avram_gclose16_original_sampled_preexit_clipped_clock_floor
      X x D hDstrat (fun ω => (σ ω : WithTop ℝ≥0))
      hσstop r hgrid (δ j)).2.2 ω (L j ω) (by simpa only [R] using hc) t ht
    have hright := dividendStrategy_le_rightLimit D hDstrat ω t
    dsimp [δ] at hz
    unfold riskProcess
    linarith
  exact ⟨L, hLstop, hLle, hLmono, hLlimit, hFloor⟩
