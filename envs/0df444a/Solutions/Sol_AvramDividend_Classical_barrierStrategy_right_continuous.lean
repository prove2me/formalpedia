-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:25:20.870861+00:00
-- url     : https://prove2.me/submissions/93fa9e53-9853-45a2-82a4-a4ec5f11e29e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

lemma P33663233_runSup_cont (g : ℝ≥0 → ℝ) (hg : ∀ t, ContinuousWithinAt g (Ici t) t)
    (t : ℝ≥0) :
    ContinuousWithinAt (fun s => ⨆ u : Icc (0:ℝ≥0) s, g u) (Ici t) t := by
  by_cases hb : BddAbove (range fun u : Icc (0:ℝ≥0) t => g u)
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.mp (hg t) (ε/2) (by linarith)
    refine ⟨δ, hδ, fun {s} hs hst => ?_⟩
    have hts : t ≤ s := hs
    have hgt : g t ≤ ⨆ u : Icc (0:ℝ≥0) t, g u :=
      le_ciSup (f := fun u : Icc (0:ℝ≥0) t => g u) hb ⟨t, ⟨zero_le, le_rfl⟩⟩
    have hbound : ∀ u : Icc (0:ℝ≥0) s, g u ≤ (⨆ u : Icc (0:ℝ≥0) t, g u) + ε/2 := by
      rintro ⟨u, hu0, hus⟩
      rcases le_total u t with hut | htu
      · have := le_ciSup (f := fun u : Icc (0:ℝ≥0) t => g u) hb ⟨u, ⟨hu0, hut⟩⟩
        simp only at this ⊢
        linarith
      · have hd : dist u t < δ := by
          have h1 : (t:ℝ) ≤ u := by exact_mod_cast htu
          have h2 : (u:ℝ) ≤ s := by exact_mod_cast hus
          rw [NNReal.dist_eq] at hst ⊢
          rw [abs_of_nonneg (by linarith)] at hst ⊢
          linarith
        have := hδε htu hd
        rw [Real.dist_eq, abs_lt] at this
        simp only
        linarith [this.2]
    have hbs : BddAbove (range fun u : Icc (0:ℝ≥0) s => g u) :=
      ⟨_, by rintro _ ⟨u, rfl⟩; exact hbound u⟩
    have hle : (⨆ u : Icc (0:ℝ≥0) s, g u) ≤ (⨆ u : Icc (0:ℝ≥0) t, g u) + ε/2 := by
      have : Nonempty (Icc (0:ℝ≥0) s) := ⟨⟨0, le_rfl, zero_le⟩⟩
      exact ciSup_le hbound
    have hge : (⨆ u : Icc (0:ℝ≥0) t, g u) ≤ (⨆ u : Icc (0:ℝ≥0) s, g u) := by
      have : Nonempty (Icc (0:ℝ≥0) t) := ⟨⟨0, le_rfl, zero_le⟩⟩
      exact ciSup_le fun u =>
        le_ciSup_of_le hbs ⟨u.1, u.2.1, u.2.2.trans hts⟩ le_rfl
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · have hc : ∀ s, t ≤ s → (⨆ u : Icc (0:ℝ≥0) s, g u) = 0 := by
      intro s hs
      apply Real.iSup_of_not_bddAbove
      rintro ⟨M, hM⟩
      apply hb
      refine ⟨M, ?_⟩
      rintro _ ⟨u, rfl⟩
      exact hM ⟨⟨u.1, u.2.1, u.2.2.trans hs⟩, rfl⟩
    have h0 : ContinuousWithinAt (fun _ : ℝ≥0 => (0:ℝ)) (Ici t) t := continuousWithinAt_const
    exact h0.congr (fun s hs => hc s hs) (hc t le_rfl)

open MeasureTheory Filter Set Topology NNReal ENNReal AvramDividend.Classical in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ) :
    ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => barrierStrategy X c c s ω) (Ici t) t := by
  intro ω t
  have hD : (fun s => barrierStrategy X c c s ω) =
      fun s => max 0 (⨆ u : Icc (0:ℝ≥0) s, X.X u ω) := by
    funext s
    unfold barrierStrategy
    split_ifs with h
    · subst h
      have hu : ∀ u : Icc (0:ℝ≥0) 0, X.X u ω = 0 := fun u => by
        have : (u:ℝ≥0) = 0 := le_antisymm u.2.2 u.2.1
        rw [this, X.X_zero]
      have : Nonempty (Icc (0:ℝ≥0) 0) := ⟨⟨0, le_rfl, le_rfl⟩⟩
      have : (⨆ u : Icc (0:ℝ≥0) 0, X.X u ω) = 0 := by
        simp only [hu, ciSup_const]
      rw [this, max_self]
    · simp
  rw [hD]
  exact (continuous_const.max continuous_id).continuousAt.comp_continuousWithinAt
    (P33663233_runSup_cont _ (X.rightCont ω) t)
