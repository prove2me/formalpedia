-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_nojump_unitdrift_path_satisfies_all_phys89b_contact_antecedents
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T15:23:59.139569+00:00
-- url     : https://prove2.me/submissions/094dc624-dbb3-4f2e-b946-495f1d43cf33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ 1 →
      X.X t ω = (t : ℝ) * X.drift)
    (hNoJump : ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))) (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0) :
    let S : ℝ≥0 := ⟨(1 / 10 : ℝ), by norm_num⟩
    (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) ∧
    (((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))) (Ioc 0 S ×ˢ Iio (0 : ℝ)) = 0) ∧
    (S : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω ∧
    (¬ (∀ t : ℝ≥0, t ≤ S →
      0 < riskProcess X 0 (barrierStrategy X 0 0) t ω ∧
      ENNReal.ofReal (riskProcess X 0 (barrierStrategy X 0 0) t ω) <
        (1 : ℝ≥0∞))) := by
  intro S
  have hS1 : S ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    show (1 / 10 : ℝ) ≤ ((1 : ℝ≥0) : ℝ)
    norm_num
  have hX : ∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) := by
    intro t ht; rw [hPath t ht, hDrift, mul_one]
  -- the supremum of the path on [0, t] equals t for t ≤ 1
  have hsup : ∀ t : ℝ≥0, t ≤ 1 → (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) = (t : ℝ) := by
    intro t ht
    have : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨t, (bot_le : (⊥ : ℝ≥0) ≤ _), le_rfl⟩⟩
    apply le_antisymm
    · refine ciSup_le fun s => ?_
      rw [hX s (s.2.2.trans ht)]
      exact_mod_cast s.2.2
    · have hb : BddAbove (Set.range fun s : Icc (0 : ℝ≥0) t => X.X s ω) := by
        refine ⟨t, ?_⟩
        rintro _ ⟨s, rfl⟩
        show X.X s ω ≤ t
        rw [hX s (s.2.2.trans ht)]
        exact_mod_cast s.2.2
      refine le_trans ?_ (le_ciSup hb ⟨t, (bot_le : (⊥ : ℝ≥0) ≤ _), le_rfl⟩)
      rw [hX t ht]
  have hrisk : ∀ t : ℝ≥0, t ≤ 1 → riskProcess X 0 (barrierStrategy X 0 0) t ω = 0 := by
    intro t ht
    unfold riskProcess barrierStrategy
    by_cases h0 : t = 0
    · subst h0; simp [X.X_zero]
    · simp only [h0, if_false, hsup t ht, hX t ht]
      have : (0 : ℝ) ≤ t := t.2
      rw [max_eq_right (by linarith)]
      ring
  refine ⟨fun t ht => hPath t (ht.trans hS1), ?_, ?_, ?_⟩
  · refine le_antisymm (le_trans (measure_mono ?_) hNoJump.le) ((by positivity))
    exact Set.prod_mono (Set.Ioc_subset_Ioc_right hS1) le_rfl
  · have h1 : (1 : ℝ≥0∞) ≤ ruinTime X 0 (barrierStrategy X 0 0) ω := by
      unfold ruinTime
      refine le_iInf₂ fun t ht => ?_
      by_contra hlt
      push_neg at hlt
      have ht1 : t ≤ 1 := by exact_mod_cast hlt.le
      rw [hrisk t ht1] at ht
      exact lt_irrefl _ ht
    refine lt_of_lt_of_le ?_ h1
    have : (S : ℝ≥0∞) = ((1/10 : ℝ≥0) : ℝ≥0∞) := by
      congr 1
    rw [this]
    exact_mod_cast (show (1/10 : ℝ≥0) < 1 by rw [← NNReal.coe_lt_coe]; norm_num)
  · intro h
    have := (h 0 ((bot_le : (⊥ : ℝ≥0) ≤ _))).1
    rw [hrisk 0 ((bot_le : (⊥ : ℝ≥0) ≤ _))] at this
    exact lt_irrefl _ this

