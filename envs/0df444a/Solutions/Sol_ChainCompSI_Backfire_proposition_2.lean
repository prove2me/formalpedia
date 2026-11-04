-- Prove2me | solution 1 for ChainCompSI.Backfire.proposition_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:23:05.625006+00:00
-- url     : https://prove2.me/submissions/df361cc3-b533-4105-baf5-cc8fe31c0428
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ChainCompSI_Backfire_table_1_ni
import Theorems.Thm_ChainCompSI_Backfire_table_1_si

open ChainCompSI.Backfire

/-- Manufacturer comparison: SI profit of Table 1 is below the NI profit whenever
`h (4+θ) < 1` and the linear factor is positive. -/
theorem chainCompSI_prop2_mfr_cmp (θ h : ℝ) (hθ : 0 < θ) (hx : h * (4 + θ) < 1)
    (hq : 0 < (1088 + 816 * θ + 220 * θ ^ 2 + 21 * θ ^ 3) * h + (-272 + 136 * θ + 55 * θ ^ 2)) :
    4 * (1 + θ) * (306 - 34 * h * (4 - θ) + h ^ 2 * (272 + θ * (136 + 21 * θ))) /
        (68 + 19 * θ) ^ 2 < 4 * (1 + θ) / (4 + θ) ^ 2 := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : 4 * (1 + θ) * (306 - 34 * h * (4 - θ) + h ^ 2 * (272 + θ * (136 + 21 * θ))) *
      (4 + θ) ^ 2 - 4 * (1 + θ) * (68 + 19 * θ) ^ 2 =
      -(4 * (1 + θ) * (1 - h * (4 + θ)) *
        ((1088 + 816 * θ + 220 * θ ^ 2 + 21 * θ ^ 3) * h + (-272 + 136 * θ + 55 * θ ^ 2))) := by
    ring
  have hp : 0 < 4 * (1 + θ) * (1 - h * (4 + θ)) *
      ((1088 + 816 * θ + 220 * θ ^ 2 + 21 * θ ^ 3) * h + (-272 + 136 * θ + 55 * θ ^ 2)) := by
    have : 0 < 1 - h * (4 + θ) := by linarith
    positivity
  linarith

/-- Retailer comparison: the SI retailer profit computed from the Table 1 values is below the
NI retailer profit whenever `h (4+θ) < 1` and the linear factor is positive. -/
theorem chainCompSI_prop2_ret_cmp (θ h w1 p1 D1 I w2 p2 D2 : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h)
    (hx : h * (4 + θ) < 1)
    (hq : 0 < (19456 + 47232 * θ + 44192 * θ ^ 2 + 21384 * θ ^ 3 + 5738 * θ ^ 4 + 819 * θ ^ 5
        + 49 * θ ^ 6) * h + (-2688 - 4544 * θ - 1576 * θ ^ 2 + 752 * θ ^ 3 + 556 * θ ^ 4
        + 84 * θ ^ 5))
    (hw1 : w1 = (36 - 2 * h * (4 - θ)) / (68 + 19 * θ))
    (hp1 : p1 = (104 + 55 * θ - 2 * h * (1 + θ) * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hD1 : D1 = (1 + θ) * (32 + 19 * θ + 2 * h * (4 - θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hI : I = (1 + θ) * (20 + 7 * θ) * (1 - h * (4 + θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hw2 : w2 = (24 + 40 * h + 14 * h * θ) / (68 + 19 * θ))
    (hp2 : p2 = (92 + 43 * θ + 2 * h * (1 + θ) * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ)))
    (hD2 : D2 = (1 + θ) * (44 + 19 * θ - 2 * h * (20 + 7 * θ)) / ((2 + θ) * (68 + 19 * θ))) :
    p1 * max D1 0 - w1 * (max D1 0 + I) - h * I +
        (p2 * max D2 0 - w2 * max (max D2 0 - I) 0) < 2 * (1 + θ) / (4 + θ) ^ 2 := by
  have hK : 0 < (2 + θ) * (68 + 19 * θ) := by positivity
  have hhθ : h * θ < 1 := by nlinarith
  have hD1pos : 0 < D1 := by
    rw [hD1]; apply div_pos _ hK
    apply mul_pos (by linarith); nlinarith
  have hI0 : 0 ≤ I := by
    rw [hI]; apply div_nonneg _ hK.le
    have : 0 ≤ 1 - h * (4 + θ) := by linarith
    positivity
  have hDI : D2 - I = (1 + θ) * (24 + 12 * θ + 40 * h + 34 * h * θ + 7 * h * θ ^ 2) /
      ((2 + θ) * (68 + 19 * θ)) := by
    rw [hD2, hI]; field_simp; ring
  have hDIpos : 0 < D2 - I := by rw [hDI]; positivity
  have hD2pos : 0 < D2 := by linarith
  rw [max_eq_left hD1pos.le, max_eq_left hD2pos.le, max_eq_left hDIpos.le]
  have hval : p1 * D1 - w1 * (D1 + I) - h * I + (p2 * D2 - w2 * (D2 - I)) =
      (2480 + 4960 * θ + 3118 * θ ^ 2 + 638 * θ ^ 3 +
        h * (-1888 - 3312 * θ - 1666 * θ ^ 2 - 207 * θ ^ 3 + 35 * θ ^ 4) +
        h ^ 2 * (4864 + 10592 * θ + 8400 * θ ^ 2 + 3246 * θ ^ 3 + 623 * θ ^ 4 + 49 * θ ^ 5)) /
        ((2 + θ) * (68 + 19 * θ)) ^ 2 := by
    rw [hw1, hp1, hD1, hI, hw2, hp2, hD2]; field_simp; ring
  rw [hval, div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : (2480 + 4960 * θ + 3118 * θ ^ 2 + 638 * θ ^ 3 +
        h * (-1888 - 3312 * θ - 1666 * θ ^ 2 - 207 * θ ^ 3 + 35 * θ ^ 4) +
        h ^ 2 * (4864 + 10592 * θ + 8400 * θ ^ 2 + 3246 * θ ^ 3 + 623 * θ ^ 4 + 49 * θ ^ 5)) *
        (4 + θ) ^ 2 - 2 * (1 + θ) * ((2 + θ) * (68 + 19 * θ)) ^ 2 =
      -((1 - h * (4 + θ)) * ((19456 + 47232 * θ + 44192 * θ ^ 2 + 21384 * θ ^ 3 + 5738 * θ ^ 4
        + 819 * θ ^ 5 + 49 * θ ^ 6) * h + (-2688 - 4544 * θ - 1576 * θ ^ 2 + 752 * θ ^ 3
        + 556 * θ ^ 4 + 84 * θ ^ 5))) := by
    ring
  have hp : 0 < (1 - h * (4 + θ)) * ((19456 + 47232 * θ + 44192 * θ ^ 2 + 21384 * θ ^ 3
      + 5738 * θ ^ 4 + 819 * θ ^ 5 + 49 * θ ^ 6) * h + (-2688 - 4544 * θ - 1576 * θ ^ 2
      + 752 * θ ^ 3 + 556 * θ ^ 4 + 84 * θ ^ 5)) := by
    have : 0 < 1 - h * (4 + θ) := by linarith
    positivity
  linarith

/-- Existence of a threshold `θ0`: both linear factors are positive on `(θ0, θ*)`. -/
theorem chainCompSI_prop2_threshold (h : ℝ) (hh : 0 ≤ h) (h4 : h < 1 / 4) :
    ∃ θ0 : ℝ, 0 ≤ θ0 ∧ h * (4 + θ0) < 1 ∧ ∀ θ : ℝ, θ0 < θ → h * (4 + θ) < 1 →
      0 < (1088 + 816 * θ + 220 * θ ^ 2 + 21 * θ ^ 3) * h + (-272 + 136 * θ + 55 * θ ^ 2) ∧
      0 < (19456 + 47232 * θ + 44192 * θ ^ 2 + 21384 * θ ^ 3 + 5738 * θ ^ 4 + 819 * θ ^ 5
        + 49 * θ ^ 6) * h + (-2688 - 4544 * θ - 1576 * θ ^ 2 + 752 * θ ^ 3 + 556 * θ ^ 4
        + 84 * θ ^ 5) := by
  rcases hh.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨3, by norm_num, by norm_num, fun θ hθ _ => ?_⟩
    obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ θ = 3 + s := ⟨θ - 3, by linarith, by ring⟩
    constructor
    · have e : (1088 + 816 * (3 + s) + 220 * (3 + s) ^ 2 + 21 * (3 + s) ^ 3) * 0 +
          (-272 + 136 * (3 + s) + 55 * (3 + s) ^ 2) = 631 + 466 * s + 55 * s ^ 2 := by ring
      rw [e]; positivity
    · have e : (19456 + 47232 * (3 + s) + 44192 * (3 + s) ^ 2 + 21384 * (3 + s) ^ 3
          + 5738 * (3 + s) ^ 4 + 819 * (3 + s) ^ 5 + 49 * (3 + s) ^ 6) * 0 +
          (-2688 - 4544 * (3 + s) - 1576 * (3 + s) ^ 2 + 752 * (3 + s) ^ 3
          + 556 * (3 + s) ^ 4 + 84 * (3 + s) ^ 5) =
          55248 + 100372 * s + 57896 * s ^ 2 + 14984 * s ^ 3 + 1816 * s ^ 4 + 84 * s ^ 5 := by
        ring
      rw [e]; positivity
  · set ts : ℝ := 1 / h - 4 with hts
    have hs1 : h * (4 + ts) = 1 := by rw [hts]; field_simp; ring
    have hts0 : 0 < ts := by
      have : 4 < 1 / h := by rw [lt_div_iff₀ hpos]; linarith
      linarith
    set qM : ℝ → ℝ := fun θ =>
      (1088 + 816 * θ + 220 * θ ^ 2 + 21 * θ ^ 3) * h + (-272 + 136 * θ + 55 * θ ^ 2) with hqM
    set qR : ℝ → ℝ := fun θ =>
      (19456 + 47232 * θ + 44192 * θ ^ 2 + 21384 * θ ^ 3 + 5738 * θ ^ 4 + 819 * θ ^ 5
        + 49 * θ ^ 6) * h + (-2688 - 4544 * θ - 1576 * θ ^ 2 + 752 * θ ^ 3 + 556 * θ ^ 4
        + 84 * θ ^ 5) with hqR
    have hM : 0 < qM ts := by
      have e : qM ts * (4 + ts) = 1088 * ts + 576 * ts ^ 2 + 76 * ts ^ 3 := by
        simp only [hqM]
        linear_combination (1088 + 816 * ts + 220 * ts ^ 2 + 21 * ts ^ 3) * hs1
      have : 0 < qM ts * (4 + ts) := by rw [e]; positivity
      exact (pos_iff_pos_of_mul_pos this).2 (by linarith)
    have hR : 0 < qR ts := by
      have e : qR ts * (4 + ts) = 8704 + 26368 * ts + 33344 * ts ^ 2 + 22816 * ts ^ 3
          + 8714 * ts ^ 4 + 1711 * ts ^ 5 + 133 * ts ^ 6 := by
        simp only [hqR]
        linear_combination (19456 + 47232 * ts + 44192 * ts ^ 2 + 21384 * ts ^ 3
          + 5738 * ts ^ 4 + 819 * ts ^ 5 + 49 * ts ^ 6) * hs1
      have : 0 < qR ts * (4 + ts) := by rw [e]; positivity
      exact (pos_iff_pos_of_mul_pos this).2 (by linarith)
    have hc : Continuous (fun θ => min (qM θ) (qR θ)) := by
      simp only [hqM, hqR]; fun_prop
    have hev : ∀ᶠ θ in nhds ts, 0 < min (qM θ) (qR θ) :=
      (hc.tendsto ts).eventually (lt_mem_nhds (lt_min hM hR))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨max 0 (ts - ε / 2), le_max_left _ _, ?_, fun θ hθ hθx => ?_⟩
    · have : max 0 (ts - ε / 2) < ts := max_lt hts0 (by linarith)
      nlinarith
    · have hlt : θ < ts := by
        by_contra hc'
        have hc'' := not_lt.mp hc'
        nlinarith
      have hgt : ts - ε / 2 < θ := lt_of_le_of_lt (le_max_right _ _) hθ
      have hd : dist θ ts < ε := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith
      have := hball hd
      exact ⟨lt_of_lt_of_le this (min_le_left _ _), lt_of_lt_of_le this (min_le_right _ _)⟩

theorem solution (h : ℝ) (hh : 0 ≤ h) : (h < 1 / 4 → ∃ θ0 : ℝ, 0 ≤ θ0 ∧ h * (4 + θ0) < 1 ∧ ∀ θ : ℝ, θ0 < θ → h * (4 + θ) < 1 → (∃ E, IsEq θ h SI E) ∧ (∃ E', IsEq θ h NI E') ∧ ∀ E E', IsEq θ h SI E → IsEq θ h NI E' → ∀ i : Fin 2, mfrProfit θ E i < mfrProfit θ E' i ∧ retProfit θ h E i < retProfit θ h E' i) ∧ (∀ θ : ℝ, 0 < θ → (1 / 4 ≤ h ∨ 1 ≤ h * (4 + θ)) → (∃ E, IsEq θ h SI E) ∧ ∀ E, IsEq θ h SI E → ∀ i : Fin 2, E.inv i = 0) := by
  refine ⟨fun h4 => ?_, fun θ hθ hcase => ?_⟩
  · obtain ⟨θ0, h0, hx0, hq⟩ := chainCompSI_prop2_threshold h hh h4
    refine ⟨θ0, h0, hx0, fun θ hθ hx => ?_⟩
    have hθpos : 0 < θ := by linarith
    obtain ⟨hSIex, hSI⟩ := table_1_si θ h hθpos hh hx.le
    obtain ⟨hNIex, hNI⟩ := table_1_ni θ h hθpos hh NI (Or.inl rfl)
    refine ⟨hSIex, hNIex, fun E E' hE hE' i => ?_⟩
    obtain ⟨hw1, hp1, hD1, hinv, hw2, hp2, hD2, hmfr⟩ := hSI E hE i
    obtain ⟨-, -, -, -, -, -, -, hmfr', hret'⟩ := hNI E' hE' i
    obtain ⟨qM, qR⟩ := hq θ hθ hx
    constructor
    · rw [hmfr, hmfr']
      exact chainCompSI_prop2_mfr_cmp θ h hθpos hx qM
    · rw [hret']
      have hD1' : demand θ (E.p1 i) (E.p1 (rival i)) = _ := hD1
      have hD2' : demand θ (E.p2' i) (E.p2' (rival i)) = _ := hD2
      unfold retProfit retP1 retP2 sales
      exact chainCompSI_prop2_ret_cmp θ h _ _ _ _ _ _ _ hθpos hh hx qR hw1 hp1 hD1' hinv hw2
        hp2 hD2'
  · have hx1 : 1 ≤ h * (4 + θ) := by
      rcases hcase with h4 | h1
      · nlinarith
      · exact h1
    rcases hx1.lt_or_eq with hlt | heq
    · obtain ⟨ex, hall⟩ := table_1_ni θ h hθ hh SI (Or.inr ⟨rfl, hlt⟩)
      exact ⟨ex, fun E hE i => (hall E hE i).2.2.2.1⟩
    · obtain ⟨ex, hall⟩ := table_1_si θ h hθ hh heq.symm.le
      refine ⟨ex, fun E hE i => ?_⟩
      rw [(hall E hE i).2.2.2.1, ← heq]
      simp
