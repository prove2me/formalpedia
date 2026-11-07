-- Prove2me | solution 1 for DualityStability.WeakDuality.biconjugation_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:46:47.126023+00:00
-- url     : https://prove2.me/submissions/d487c587-33af-4476-96c8-bef972a653a5

import Theorems.Thm_DualityStability_WeakDuality_hull_lsc_convex

open Filter Topology DualityStability.WeakDuality

section FM

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

lemma ds2_epi_closed (φ : F → EReal) (hlsc : LowerSemicontinuous φ) :
    IsClosed {p : F × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨y, μ⟩ hp
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hp
  have hr1' : μ < r := by exact_mod_cast hr1
  have hev : ∀ᶠ z in 𝓝 y, (r : EReal) < φ z := hlsc y r hr2
  filter_upwards [prod_mem_nhds hev (Iio_mem_nhds hr1')]
  rintro ⟨z, ν⟩ ⟨hz, hν⟩ hzν
  simp only [Set.mem_setOf_eq, Set.mem_Iio] at hz hν hzν
  have : (r : EReal) < ν := lt_of_lt_of_le hz hzν
  have : r < ν := by exact_mod_cast this
  linarith

lemma ds2_sep (φ : F → EReal) (hlsc : LowerSemicontinuous φ) (hconv : EpigraphConvex φ)
    (y1 : F) (m1 : ℝ) (hy1 : φ y1 = m1)
    (y0 : F) (r : ℝ) (hr : (r : EReal) < φ y0) :
    ∃ (ℓ : F →L[ℝ] ℝ) (c u : ℝ), (∀ (y : F) (μ : ℝ), φ y ≤ μ → ℓ y + μ * c < u) ∧
      u < ℓ y0 + r * c ∧ c ≤ 0 := by
  have hnot : (y0, r) ∉ {p : F × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, not_le]; exact hr
  obtain ⟨L, u, hL, hu⟩ := geometric_hahn_banach_closed_point hconv (ds2_epi_closed φ hlsc) hnot
  set ℓ : F →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ F ℝ) with hℓ
  set c : ℝ := L (0, 1) with hc
  have hdec : ∀ (y : F) (μ : ℝ), L (y, μ) = ℓ y + μ * c := by
    intro y μ
    have : ((y, μ) : F × ℝ) = (y, 0) + μ • ((0 : F), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [hℓ, hc]
  refine ⟨ℓ, c, u, fun y μ h => ?_, ?_, ?_⟩
  · rw [← hdec]; exact hL _ h
  · rw [← hdec]; exact hu
  · by_contra hcpos
    rw [not_le] at hcpos
    set μ : ℝ := max m1 ((u - ℓ y1) / c) with hμ
    have hmem : φ y1 ≤ (μ : EReal) := by
      rw [hy1]; exact_mod_cast le_max_left _ _
    have h1 := hL (y1, μ) hmem
    rw [hdec] at h1
    have h2 : (u - ℓ y1) / c ≤ μ := le_max_right _ _
    rw [div_le_iff₀ hcpos] at h2
    linarith

lemma ds2_affine_of_neg (φ : F → EReal) (ℓ : F →L[ℝ] ℝ) (c u : ℝ) (y0 : F) (r : ℝ)
    (h1 : ∀ (y : F) (μ : ℝ), φ y ≤ μ → ℓ y + μ * c < u) (h2 : u < ℓ y0 + r * c)
    (hc : c < 0) :
    ∃ (ℓ' : F →L[ℝ] ℝ) (β : ℝ), (∀ y, ((ℓ' y + β : ℝ) : EReal) ≤ φ y) ∧ r < ℓ' y0 + β := by
  refine ⟨(-c⁻¹) • ℓ, u / c, ?_, ?_⟩
  · intro y
    have heq : ((-c⁻¹) • ℓ) y + u / c = (u - ℓ y) / c := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; field_simp; ring
    rw [heq]
    by_cases htop : φ y = ⊤
    · rw [htop]; exact le_top
    · by_cases hbot : φ y = ⊥
      · -- then every real μ is above φ y
        have := h1 y ((u - ℓ y) / c - 1) (by rw [hbot]; exact bot_le)
        have h3 : ((u - ℓ y) / c - 1) * c = (u - ℓ y) - c := by
          rw [sub_mul, div_mul_cancel₀ _ hc.ne]; ring
        rw [h3] at this; linarith
      · rw [← EReal.coe_toReal htop hbot]
        have := h1 y (φ y).toReal (le_of_eq (EReal.coe_toReal htop hbot).symm)
        have : (u - ℓ y) / c ≤ (φ y).toReal := by
          rw [div_le_iff_of_neg hc]; linarith
        exact_mod_cast this
  · have heq : ((-c⁻¹) • ℓ) y0 + u / c = (u - ℓ y0) / c := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; field_simp; ring
    rw [heq, lt_div_iff_of_neg hc]; linarith

lemma ds2_minorant (φ : F → EReal) (hlsc : LowerSemicontinuous φ) (hconv : EpigraphConvex φ)
    (hprop : Proper φ) (y0 : F) (r : ℝ) (hr : (r : EReal) < φ y0) :
    ∃ (ℓ' : F →L[ℝ] ℝ) (β : ℝ), (∀ y, ((ℓ' y + β : ℝ) : EReal) ≤ φ y) ∧ r < ℓ' y0 + β := by
  obtain ⟨hnb, y1, hy1⟩ := hprop
  set m1 := (φ y1).toReal with hm1
  have hy1r : φ y1 = m1 := (EReal.coe_toReal hy1 (hnb y1)).symm
  obtain ⟨ℓ, c, u, h1, h2, hc⟩ := ds2_sep φ hlsc hconv y1 m1 hy1r y0 r hr
  rcases hc.lt_or_eq with hc | hc
  · exact ds2_affine_of_neg φ ℓ c u y0 r h1 h2 hc
  · -- vertical case: build a minorant at `y1` first
    subst hc
    obtain ⟨ℓ1, c1, u1, h11, h12, hc1⟩ := ds2_sep φ hlsc hconv y1 m1 hy1r y1 (m1 - 1)
      (by rw [hy1r]; exact_mod_cast (by linarith : m1 - 1 < m1))
    have hc1' : c1 < 0 := by
      rcases hc1.lt_or_eq with h | h
      · exact h
      · subst h
        have := h11 y1 m1 (le_of_eq hy1r)
        simp at this h12; linarith
    obtain ⟨ℓa, βa, hmin, -⟩ := ds2_affine_of_neg φ ℓ1 c1 u1 y1 (m1 - 1) h11 h12 hc1'
    simp only [mul_zero, add_zero] at h1 h2
    have hpos : 0 < ℓ y0 - u := by linarith
    set t : ℝ := max 0 ((r - βa - ℓa y0) / (ℓ y0 - u)) + 1 with ht
    have ht0 : 0 < t := by have := le_max_left 0 ((r - βa - ℓa y0) / (ℓ y0 - u)); linarith
    have ht1 : (r - βa - ℓa y0) / (ℓ y0 - u) < t := by
      have := le_max_right 0 ((r - βa - ℓa y0) / (ℓ y0 - u)); linarith
    refine ⟨ℓa + t • ℓ, βa - t * u, ?_, ?_⟩
    · intro y
      by_cases htop : φ y = ⊤
      · rw [htop]; exact le_top
      · have hyr : φ y = ((φ y).toReal : EReal) := (EReal.coe_toReal htop (hnb y)).symm
        have hly := h1 y (φ y).toReal (le_of_eq hyr)
        refine le_trans ?_ (hmin y)
        have : (ℓa + t • ℓ) y + (βa - t * u) ≤ ℓa y + βa := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
          nlinarith
        exact_mod_cast this
    · rw [div_lt_iff₀ hpos] at ht1
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith

end FM

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

theorem solution (P : Problem E E' F F')
    (hproper : Proper P.hull) :
    P.hull 0 = ⨆ y' : F', (P.pairF.pair (0 : F) y' : EReal) - P.hullConjugate y' := by
  obtain ⟨hlsc, hconv⟩ := hull_lsc_convex P
  simp only [map_zero, LinearMap.zero_apply, EReal.coe_zero, zero_sub]
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    obtain ⟨ℓ, β, hmin, hrβ⟩ := ds2_minorant P.hull hlsc hconv hproper 0 r hr2
    obtain ⟨y', hy', -⟩ := P.pairF.represents_left ℓ
    have hconj : P.hullConjugate y' ≤ ((-β : ℝ) : EReal) := by
      refine iSup_le fun y => ?_
      rw [hy' y]
      apply EReal.sub_le_of_le_add
      calc ((ℓ y : ℝ) : EReal) = ((-β : ℝ) : EReal) + ((ℓ y + β : ℝ) : EReal) := by
            rw [← EReal.coe_add]; congr 1; ring
        _ ≤ ((-β : ℝ) : EReal) + P.hull y := by gcongr; exact hmin y
    have hge : ((β : ℝ) : EReal) ≤ -P.hullConjugate y' := by
      rw [EReal.le_neg]; simpa using hconj
    have hsup := le_iSup (fun y' : F' => -P.hullConjugate y') y'
    simp only [map_zero, zero_add] at hrβ
    have : (r : EReal) < β := by exact_mod_cast hrβ
    exact absurd (lt_of_lt_of_le hr1 (le_trans (le_trans this.le hge) hsup)) (lt_irrefl _)
  · refine iSup_le fun y' => ?_
    rw [EReal.neg_le]
    have := le_iSup (fun y : F => (P.pairF.pair y y' : EReal) - P.hull y) 0
    simpa [Problem.hullConjugate] using this
