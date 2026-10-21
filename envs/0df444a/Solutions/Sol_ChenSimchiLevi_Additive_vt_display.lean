-- Prove2me | solution 1 for ChenSimchiLevi.Additive.vt_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:51:30.746719+00:00
-- url     : https://prove2.me/submissions/f946e261-9288-44a6-b732-2de05dcbed70

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_Model

set_option autoImplicit false

open Filter ChenSimchiLevi.Additive

theorem solution (k c : ℝ) (G : ℝ → ℝ) (hk : 0 ≤ k) (hGcont : Continuous G)
    (hGtop : Tendsto G atTop atBot) (hGbot : Tendsto G atBot atBot)
    (hGk : BertsekasKConvex k (fun y => -G y)) :
    ∃ s S : ℝ, s ≤ S ∧ IsMaxOn G Set.univ S ∧ IsLeast {y : ℝ | G S = G y + k} s ∧
      (∀ x : ℝ, x ≤ s →
        c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) = -k + G S + c * x) ∧
      (∀ x : ℝ, s ≤ x →
        c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) = G x + c * x) ∧
      BertsekasKConvex k
        (fun x => -(c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x))) := by
  -- k-concavity of G in the usual form
  have hGk' : ∀ z b y : ℝ, 0 ≤ z → 0 < b →
      G (z + y) ≤ k + G y + (z / b) * (G y - G (y - b)) := by
    intro z b y hz hb
    have := hGk z b y hz hb
    simp only at this
    have e : z / b * (-G y - -G (y - b)) = -(z / b * (G y - G (y - b))) := by ring
    linarith
  -- a global maximiser
  obtain ⟨S, hS⟩ : ∃ S, ∀ y, G y ≤ G S := by
    apply Continuous.exists_forall_ge hGcont
    rw [cocompact_eq_atBot_atTop]
    exact hGbot.sup hGtop
  -- the left tail
  obtain ⟨N, hN⟩ : ∃ N, ∀ y ≤ N, G y < G S - k := by
    have := hGbot.eventually (eventually_lt_atBot (G S - k))
    exact eventually_atBot.mp this
  -- the set Z
  set Z : Set ℝ := {y : ℝ | G S = G y + k} with hZ
  have hZclosed : IsClosed Z := isClosed_eq continuous_const (hGcont.add continuous_const)
  have hZbdd : BddBelow Z := by
    refine ⟨N, fun y hy => ?_⟩
    by_contra h
    push_neg at h
    have := hN y h.le
    have hy' : G S = G y + k := hy
    linarith
  have hIVT : ∀ y, G S - k ≤ G y → ∃ y' ∈ Set.Icc (min N y) y, G y' = G S - k := by
    intro y hy
    have hlt : G (min N y) < G S - k := hN _ (min_le_left _ _)
    have := intermediate_value_Icc (min_le_right N y) hGcont.continuousOn
      (show G S - k ∈ Set.Icc (G (min N y)) (G y) from ⟨hlt.le, hy⟩)
    obtain ⟨y', hy', hy'e⟩ := this
    exact ⟨y', hy', hy'e⟩
  obtain ⟨y0, hy0, hy0e⟩ := hIVT S (by linarith [hS S])
  have hZne : Z.Nonempty := ⟨y0, by show G S = G y0 + k; linarith⟩
  have hZleast : IsLeast Z (sInf Z) := hZclosed.isLeast_csInf hZne hZbdd
  obtain ⟨s, hs⟩ : ∃ s, s = sInf Z := ⟨_, rfl⟩
  rw [← hs] at hZleast
  have hsZ : G S = G s + k := hZleast.1
  have hsy0 : s ≤ y0 := hZleast.2 (by show G S = G y0 + k; linarith)
  have hsS : s ≤ S := le_trans hsy0 hy0.2
  have hbelow : ∀ y ≤ s, G y ≤ G S - k := by
    intro y hy
    by_contra hlt
    push_neg at hlt
    obtain ⟨y', hy', hy'e⟩ := hIVT y hlt.le
    have h1 : s ≤ y' := hZleast.2 (by show G S = G y' + k; linarith)
    have h2 : y' ≤ y := hy'.2
    have : y' = y := by linarith
    subst this
    linarith
  have hmid : ∀ x, s ≤ x → x ≤ S → G S - k ≤ G x := by
    intro x hsx hxS
    rcases hsx.eq_or_lt with h | h
    · subst h; linarith
    · by_contra hlt
      push_neg at hlt
      have := hGk' (S - x) (x - s) x (by linarith) (by linarith)
      have e1 : S - x + x = S := by ring
      have e2 : x - (x - s) = s := by ring
      rw [e1, e2] at this
      have ht : (S - x) / (x - s) * (G x - G s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
  have hright : ∀ x y, s ≤ x → x < y → G y ≤ G x + k := by
    intro x y hsx hxy
    rcases le_or_gt x S with hxS | hxS
    · have := hmid x hsx hxS
      have := hS y
      linarith
    · have := hGk' (y - x) (x - S) x (by linarith) (by linarith)
      have e1 : y - x + x = y := by ring
      have e2 : x - (x - S) = S := by ring
      rw [e1, e2] at this
      have ht : (y - x) / (x - S) * (G x - G S) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith) (by linarith))
          (by linarith [hS x])
      linarith
  have hdel0 : ∀ x : ℝ, delta (x - x) = 0 := fun x => by simp [delta]
  have hdel1 : ∀ x y : ℝ, x < y → delta (y - x) = 1 := fun x y h => by
    simp [delta, h]
  -- the suprema
  have hsup1 : ∀ x, x ≤ s →
      sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) = -k + G S := by
    intro x hx
    apply IsGreatest.csSup_eq
    refine ⟨?_, ?_⟩
    · by_cases hxS : x < S
      · exact ⟨S, hxS.le, by simp only [hdel1 x S hxS]; ring⟩
      · have hxs : x = S := le_antisymm (le_trans hx hsS) (not_lt.mp hxS)
        have hss : s = S := le_antisymm hsS (by linarith)
        have hk0 : k = 0 := by
          have : G S = G s + k := hsZ
          rw [hss] at this
          linarith
        refine ⟨x, Set.mem_Ici.mpr le_rfl, ?_⟩
        simp only [hdel0, hk0, hxs]
        ring
    · rintro _ ⟨y, hy, rfl⟩
      rcases (Set.mem_Ici.mp hy).eq_or_lt with h | h
      · subst h
        simp only [hdel0]
        have := hbelow x hx
        linarith
      · simp only [hdel1 x y h]
        linarith [hS y]
  have hsup2 : ∀ x, s ≤ x →
      sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) = G x := by
    intro x hx
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, Set.mem_Ici.mpr le_rfl, ?_⟩, ?_⟩
    · simp only [hdel0]; ring
    · rintro _ ⟨y, hy, rfl⟩
      rcases (Set.mem_Ici.mp hy).eq_or_lt with h | h
      · subst h
        simp only [hdel0]
        linarith
      · simp only [hdel1 x y h]
        linarith [hright x y hx h]
  have hH : ∀ x, c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x) =
      c * x + G (max x s) := by
    intro x
    rcases le_or_gt x s with h | h
    · rw [hsup1 x h, max_eq_right h]
      linarith
    · rw [hsup2 x h.le, max_eq_left h.le]
  refine ⟨s, S, hsS, isMaxOn_univ_iff.mpr hS, hZleast, ?_, ?_, ?_⟩
  · intro x hx
    rw [hsup1 x hx]; ring
  · intro x hx
    rw [hsup2 x hx]; ring
  · have hfun : (fun x => -(c * x + sSup ((fun y => -k * delta (y - x) + G y) '' Set.Ici x))) =
        fun x => -(c * x + G (max x s)) := funext fun x => by rw [hH x]
    rw [hfun]
    -- V inequality
    have hV : ∀ z b y : ℝ, 0 ≤ z → 0 < b →
        G (max (z + y) s) ≤ k + G (max y s) + (z / b) * (G (max y s) - G (max (y - b) s)) := by
      intro z b y hz hb
      rcases le_or_gt s (y - b) with h1 | h1
      · have e1 : max (y - b) s = y - b := max_eq_left h1
        have e2 : max y s = y := max_eq_left (by linarith)
        have e3 : max (z + y) s = z + y := max_eq_left (by linarith)
        rw [e1, e2, e3]
        exact hGk' z b y hz hb
      rcases le_or_gt y s with h2 | h2
      · have e1 : max (y - b) s = s := max_eq_right (by linarith)
        have e2 : max y s = s := max_eq_right h2
        rw [e1, e2]
        have := hS (max (z + y) s)
        have : (z / b) * (G s - G s) = 0 := by ring
        linarith
      · have e1 : max (y - b) s = s := max_eq_right h1.le
        have e2 : max y s = y := max_eq_left h2.le
        have e3 : max (z + y) s = z + y := max_eq_left (by linarith)
        rw [e1, e2, e3]
        have hb' : 0 < y - s := by linarith
        have key := hGk' z (y - s) y hz hb'
        have e4 : y - (y - s) = s := by ring
        rw [e4] at key
        by_cases hGy : G y < G s
        · have hzz : z / b ≤ z / (y - s) := div_le_div_of_nonneg_left hz hb' (by linarith)
          have : (z / (y - s)) * (G y - G s) ≤ (z / b) * (G y - G s) :=
            mul_le_mul_of_nonpos_right hzz (by linarith)
          linarith
        · push_neg at hGy
          have : 0 ≤ (z / b) * (G y - G s) :=
            mul_nonneg (div_nonneg hz hb.le) (by linarith)
          have := hS (z + y)
          linarith
    intro z b y hz hb
    have := hV z b y hz hb
    have hb0 : b ≠ 0 := hb.ne'
    simp only
    have e : z / b * (-(c * y + G (max y s)) - -(c * (y - b) + G (max (y - b) s))) =
        -(c * z) - z / b * (G (max y s) - G (max (y - b) s)) := by
      field_simp
      ring
    have e2 : c * (z + y) = c * z + c * y := by ring
    rw [e]
    linarith
