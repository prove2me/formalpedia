-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys16_original_firstjump_straddling_cash_atom_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:53:51.447362+00:00
-- url     : https://prove2.me/submissions/893633e9-65e2-48e8-beea-7bd76b1ec81a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At the first negative source jump the strict zero-contact drift cash
    and the single endpoint dividend atom are kept distinct. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (s J : ℝ≥0), s < J → J ≤ H →
      (J : WithTop ℝ≥0) ≤
        (⨅ u : ℝ≥0,
          if 0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
          then (u : WithTop ℝ≥0) else ⊤) →
      ∀ (a : ℕ → ℝ≥0),
      (∀ n, s ≤ a n ∧ a n < J) →
      Monotone (fun n : ℕ => Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) →
      (⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) =
        Ioo (s : ℝ) (J : ℝ) →
      (∀ u : ℝ≥0, s ≤ u → u < J →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
      (∫⁻ t in Ioc (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) +
      (∫⁻ t in ({(J : ℝ)} : Set ℝ), f t
        ∂(dividendMeasure D ω)) := by
  filter_upwards [
    avram_bv_zero13_original_strict_prejump_zero_cash_of_first_source_jump
      X hBV hFinite hDrift x C D hD H hH
  ] with ω hω
  intro s J hsj hJH hBefore a ha hMono hCover hZero f hf
  have hStrict := hω s J hsj hJH hBefore a ha hMono hCover hZero f hf
  have hSplit :
      Ioc (s : ℝ) (J : ℝ) =
        Ioo (s : ℝ) (J : ℝ) ∪ ({(J : ℝ)} : Set ℝ) := by
    ext r
    simp only [Set.mem_Ioc, Set.mem_Ioo, Set.mem_union,
      Set.mem_singleton_iff]
    constructor
    · intro hr
      rcases lt_or_eq_of_le hr.2 with h | h
      · exact Or.inl ⟨hr.1, h⟩
      · exact Or.inr h
    · intro hr
      rcases hr with h | h
      · exact ⟨h.1, le_of_lt h.2⟩
      · subst r
        exact ⟨by exact_mod_cast hsj, le_rfl⟩
  have hDisjoint :
      Disjoint (Ioo (s : ℝ) (J : ℝ))
        ({(J : ℝ)} : Set ℝ) := by
    apply Set.disjoint_left.mpr
    intro r hr hrJ
    have hrlt : r < (J : ℝ) := hr.2
    have hrEq : r = (J : ℝ) := by simpa using hrJ
    exact (lt_irrefl (J : ℝ)) (hrEq ▸ hrlt)
  calc
    (∫⁻ t in Ioc (s : ℝ) (J : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ) ∪
          ({(J : ℝ)} : Set ℝ), f t
        ∂(dividendMeasure D ω)) := by rw [hSplit]
    _ = (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
          ∂(dividendMeasure D ω)) +
        (∫⁻ t in ({(J : ℝ)} : Set ℝ), f t
          ∂(dividendMeasure D ω)) := by
      exact lintegral_union (measurableSet_singleton (J : ℝ)) hDisjoint
    _ = _ := by rw [hStrict]
