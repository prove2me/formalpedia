-- Prove2me | solution 1 for FreePlayPremium.OptimalPolicies.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:53:29.573413+00:00
-- url     : https://prove2.me/submissions/be1e84a4-657f-4dd4-8c34-6b8414f586c7

import Definitions.Def_FreePlayPremium_OptimalPolicies_Players

open Set

open FreePlayPremium.OptimalPolicies in
theorem solution (P : PlayerParameters) (hP : P.Valid) (hdu : P.down < P.up)
    (p : ℝ) (hp : 0 ≤ p) :
    premiumShare P p ∈ Icc (0 : ℝ) 1 ∧
    ∀ s ∈ Icc (0 : ℝ) 1, SelectedStable P p s ↔ s = premiumShare P p := by
  have hnot : ¬ P.up < P.down := not_lt.mpr hdu.le
  have hd0 : 0 < P.down := hP.1
  have hstab : ∀ s, Stable P p s ↔ (s = 0 ∧ P.down - p < 0) ∨ (s = 1 ∧ 0 < P.up - p) := by
    intro s
    unfold Stable utilityDifference
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨-, -, -, h4⟩)
      · exact Or.inl ⟨h1, by linarith⟩
      · exact Or.inr ⟨h1, by linarith⟩
      · exact absurd h4 hnot
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, by linarith⟩
      · exact Or.inr (Or.inl ⟨h1, by linarith⟩)
  unfold premiumShare
  rw [if_neg hnot]
  by_cases hpd : p ≤ P.down
  · rw [if_pos hpd]
    refine ⟨⟨zero_le_one, le_refl _⟩, fun s _ => ?_⟩
    constructor
    · rintro ⟨hst, -⟩
      rcases (hstab s).mp hst with ⟨-, h⟩ | ⟨h, -⟩
      · exfalso
        linarith
      · exact h
    · rintro rfl
      refine ⟨(hstab 1).mpr (Or.inr ⟨rfl, by linarith⟩), fun z hz => ?_⟩
      rcases (hstab z).mp hz with ⟨-, h⟩ | ⟨rfl, -⟩
      · exfalso
        linarith
      · exact le_refl _
  · rw [if_neg hpd]
    push_neg at hpd
    refine ⟨⟨le_refl _, zero_le_one⟩, fun s _ => ?_⟩
    constructor
    · rintro ⟨hst, hmax⟩
      rcases (hstab s).mp hst with ⟨h, -⟩ | ⟨rfl, -⟩
      · exact h
      · exfalso
        have h0 := hmax 0 ((hstab 0).mpr (Or.inl ⟨rfl, by linarith⟩))
        unfold averageUtilityWithoutFriction at h0
        linarith
    · rintro rfl
      refine ⟨(hstab 0).mpr (Or.inl ⟨rfl, by linarith⟩), fun z hz => ?_⟩
      rcases (hstab z).mp hz with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact le_refl _
      · unfold averageUtilityWithoutFriction
        linarith
