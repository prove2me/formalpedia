-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:41:20.438325+00:00
-- url     : https://prove2.me/submissions/e0eb90ed-b3e7-47e2-8562-1374c827f099

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A larger cutoff's genuinely original compensated jump sum differs from
the smaller cutoff by precisely the source marked-measure strip and its drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) (hnm : n ≤ m)
    (T : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let S : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω =
      (∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) -
        (T : ℝ) * (∫ z in S, z ∂X.ν) := by
  intro j NX S
  let B : ℕ → Set ℝ := fun k =>
    Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1)))
  let E : ℕ → Set (ℝ≥0 × ℝ) := fun k => Ioc 0 T ×ˢ B k
  have hnR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have hnPos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmPos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hCut : -(1 / ((n : ℝ) + 1)) ≤ -(1 / ((m : ℝ) + 1)) := by
    have hFrac : (1 : ℝ) / ((m : ℝ) + 1) ≤
        1 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ hmPos hnPos).2
      nlinarith [hnR]
    linarith
  have hLower : (-1 : ℝ) ≤ -(1 / ((n : ℝ) + 1)) := by
    have hFrac : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hnPos).2
      nlinarith [hn0]
    linarith
  have hBsub : B n ⊆ B m := by
    intro z hz
    exact ⟨hz.1, le_trans hz.2 hCut⟩
  have hBdiff : B m \ B n = S := by
    ext z
    simp only [B, S, mem_diff, mem_Ioc]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hnot⟩
      refine ⟨?_, hhi⟩
      by_contra h
      exact hnot ⟨hlo, le_of_not_gt h⟩
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨lt_of_le_of_lt hLower hlo, hhi⟩, ?_⟩
      rintro ⟨_, hhiN⟩
      exact (not_le.mpr hlo) hhiN
  have hEsub : E n ⊆ E m := by
    intro p hp
    exact ⟨hp.1, hBsub hp.2⟩
  have hEdiff : E m \ E n = Ioc 0 T ×ˢ S := by
    ext p
    change ((p ∈ E m) ∧ ¬ (p ∈ E n)) ↔
      (p ∈ Ioc 0 T ×ˢ S)
    constructor
    · rintro ⟨⟨ht, hmB⟩, hnot⟩
      refine ⟨ht, ?_⟩
      rw [← hBdiff]
      exact ⟨hmB, fun hnB => hnot ⟨ht, hnB⟩⟩
    · rintro ⟨ht, hstrip⟩
      have hd : p.2 ∈ B m \ B n := by
        rwa [hBdiff]
      refine ⟨⟨ht, hd.1⟩, ?_⟩
      intro hp
      exact hd.2 hp.2
  have hEmeas : MeasurableSet (E n) := by
    dsimp [E, B]
    exact measurableSet_Ioc.prod measurableSet_Ioc
  have hBmeas : MeasurableSet (B n) := by
    dsimp [B]
    exact measurableSet_Ioc
  have hEint : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2) (E m) NX := by
    simpa only [E, B, NX, j] using
      (avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable X ω T m)
  have hBint : IntegrableOn (fun z : ℝ => z) (B m) X.ν := by
    simpa only [B] using
      (avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
        X (1 / ((m : ℝ) + 1)) (by positivity))
  have hStrip :
      (∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) =
        (∫ p in E m, p.2 ∂NX) -
          (∫ p in E n, p.2 ∂NX) := by
    rw [← hEdiff]
    exact setIntegral_sdiff hEmeas hEint hEsub
  have hDrift :
      (∫ z in S, z ∂X.ν) =
        (∫ z in B m, z ∂X.ν) -
          (∫ z in B n, z ∂X.ν) := by
    rw [← hBdiff]
    exact setIntegral_sdiff hBmeas hBint hBsub
  change
      ((∫ p in E m, p.2 ∂NX) -
        (T : ℝ) * (∫ z in B m, z ∂X.ν)) -
      ((∫ p in E n, p.2 ∂NX) -
        (T : ℝ) * (∫ z in B n, z ∂X.ν)) =
      (∫ p in (Ioc 0 T ×ˢ S), p.2 ∂NX) -
        (T : ℝ) * (∫ z in S, z ∂X.ν)
  rw [hStrip, hDrift]
  ring
