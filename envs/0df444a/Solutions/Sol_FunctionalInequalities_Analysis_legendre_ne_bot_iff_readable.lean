-- Prove2me | solution 1 for FunctionalInequalities.Analysis.legendre_ne_bot_iff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:16.796211+00:00
-- url     : https://prove2.me/submissions/b7a58e70-b088-4a62-b820-8c9a4e4d3271

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Nonemptiness of the primal's effective domain is exactly what excludes
negative infinity in its conjugate. Input values `-∞` need not be ruled out. -/
theorem solution (φ : E → EReal) (y : E) :
    FunctionalInequalities.Analysis.legendre φ y ≠ ⊥ ↔ ∃ x, φ x ≠ ⊤ := by
  constructor
  · intro h
    by_contra hnone
    have htop : ∀ x, φ x = ⊤ := by simpa only [not_exists, not_not] using hnone
    have hbottom : FunctionalInequalities.Analysis.legendre φ y = ⊥ := by simp [FunctionalInequalities.Analysis.legendre, htop]
    exact h hbottom
  · rintro ⟨x, hx⟩
    by_cases hb : φ x = ⊥
    · have htop : FunctionalInequalities.Analysis.legendre φ y = ⊤ := by
        apply eq_top_iff.mpr
        change (⊤ : EReal) ≤ ⨆ z : E, (inner ℝ z y : EReal) - φ z
        simpa only [hb, EReal.coe_sub_bot] using
          (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
      simp only [htop, ne_eq, top_ne_bot, not_false_eq_true]
    · lift φ x to ℝ using ⟨hx, hb⟩ with r hr
      have hbound : ((inner ℝ x y - r : ℝ) : EReal) ≤ FunctionalInequalities.Analysis.legendre φ y := by
        change ((inner ℝ x y - r : ℝ) : EReal) ≤
          ⨆ z : E, (inner ℝ z y : EReal) - φ z
        simpa only [← hr, EReal.coe_sub] using
          (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
      exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hbound)
