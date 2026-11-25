-- Prove2me | solution 1 for ConstrainedDirSep.STSep.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-25T06:12:14.095879+00:00
-- url     : https://prove2.me/submissions/87ff114c-dceb-45bd-9dd8-12fe7254705d

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant

open ConstrainedDirSep ConstrainedDirSep.STSep

namespace P2MHole01_dafcb711
theorem solution (x y x' y' dX dY : ℕ) (hxy : (1 : ℕ) ≤ x ∧ x ≤ dX ∧ (1 : ℕ) ≤ y ∧ y ≤ dY)
  (hx'y' : (1 : ℕ) ≤ x' ∧ x' ≤ dX ∧ (1 : ℕ) ≤ y' ∧ y' ≤ dY) :
  ((1 : ℕ) ≤ min x x' ∧ min x x' ≤ dX ∧ (1 : ℕ) ≤ min y y' ∧ min y y' ≤ dY) ∧
    (1 : ℕ) ≤ max x x' ∧ max x x' ≤ dX ∧ (1 : ℕ) ≤ max y y' ∧ max y y' ≤ dY := by
  omega
end P2MHole01_dafcb711

/-- The box `1 ≤ x ≤ dX ∧ 1 ≤ y ≤ dY` is closed under coordinatewise min and max. -/
theorem box_minmax (x y x' y' : ℕ) (dX dY : ℕ)
    (hxy : 1 ≤ x ∧ x ≤ dX ∧ 1 ≤ y ∧ y ≤ dY) (hx'y' : 1 ≤ x' ∧ x' ≤ dX ∧ 1 ≤ y' ∧ y' ≤ dY) :
    (1 ≤ min x x' ∧ min x x' ≤ dX ∧ 1 ≤ min y y' ∧ min y y' ≤ dY) ∧
    (1 ≤ max x x' ∧ max x x' ≤ dX ∧ 1 ≤ max y y' ∧ max y y' ≤ dY) := by
  (first | exact P2MHole01_dafcb711.solution x y x' y' dX dY hxy hx'y' | (apply P2MHole01_dafcb711.solution <;> assumption))

namespace P2MHole02_68b18056
theorem solution (a b x y x' y' : ℕ) (hxy : (Quadrant.se a b).Holds x y)
  (hx'y' : (Quadrant.se a b).Holds x' y') :
  (Quadrant.se a b).Holds (min x x') (min y y') ∧ (Quadrant.se a b).Holds (max x x') (max y y') := by
  -- (Quadrant.se a b).Holds u v unfolds to ¬(a ≤ u ∧ v ≤ b)
  have hxy'   : ¬ (a ≤ x  ∧ y  ≤ b) := hxy
  have hx'y'' : ¬ (a ≤ x' ∧ y' ≤ b) := hx'y'
  constructor
  · -- Show ¬(a ≤ min x x' ∧ min y y' ≤ b)
    intro h
    -- h.1 : a ≤ min x x', so a ≤ x and a ≤ x'
    have hax  : a ≤ x  := le_trans h.1 (min_le_left x x')
    have hax' : a ≤ x' := le_trans h.1 (min_le_right x x')
    -- Combined with hxy' and hx'y', this forces y > b and y' > b
    have hnb  : ¬ (y ≤ b)  := fun hh => hxy' ⟨hax, hh⟩
    have hnb' : ¬ (y' ≤ b) := fun hh => hx'y'' ⟨hax', hh⟩
    -- Case on min y y'
    rcases le_total y y' with hy'le | hyle
    · -- y ≤ y', so min y y' = y
      have hmin : min y y' = y := min_eq_left hy'le
      exact hnb (by simpa [hmin] using h.2)
    · -- y' ≤ y, so min y y' = y'
      have hmin : min y y' = y' := min_eq_right hyle
      exact hnb' (by simpa [hmin] using h.2)
  · -- Show ¬(a ≤ max x x' ∧ max y y' ≤ b)
    intro h
    -- h.2 : max y y' ≤ b, so y ≤ b and y' ≤ b
    have hy  : y ≤ b  := le_trans (le_max_left y y') h.2
    have hy' : y' ≤ b := le_trans (le_max_right y y') h.2
    -- h.1 : a ≤ max x x'. Case on x and x'.
    rcases le_total x x' with hxle | hx'le
    · -- x ≤ x', so max x x' = x'; get a ≤ x', contradicting hx'y''
      have hax' : a ≤ x' := by simpa [max_eq_right hxle] using h.1
      exact hx'y'' ⟨hax', hy'⟩
    · -- x' ≤ x, so max x x' = x; get a ≤ x, contradicting hxy'
      have hax : a ≤ x := by simpa [max_eq_left hx'le] using h.1
      exact hxy' ⟨hax, hy⟩
end P2MHole02_68b18056

-- riskiest
/-- The relation `Holds (.se a b) : ¬(a ≤ x ∧ y ≤ b)` is closed under coordinatewise
min and max: two points satisfying it imply their coordinatewise min and max do. -/
theorem se_holds_minmax (a b x y x' y' : ℕ)
    (hxy : (Quadrant.se a b).Holds x y) (hx'y' : (Quadrant.se a b).Holds x' y') :
    (Quadrant.se a b).Holds (min x x') (min y y') ∧
    (Quadrant.se a b).Holds (max x x') (max y y') := by
  (first | exact P2MHole02_68b18056.solution a b x y x' y' hxy hx'y' | (apply P2MHole02_68b18056.solution <;> assumption))

namespace P2MHole03_c5d429c1
theorem solution (a b x y x' y' : ℕ) (hxy : (Quadrant.nw a b).Holds x y)
  (hx'y' : (Quadrant.nw a b).Holds x' y') :
  (Quadrant.nw a b).Holds (min x x') (min y y') ∧ (Quadrant.nw a b).Holds (max x x') (max y y') := by
  constructor
  · intro h
    have h1 : min x x' ≤ a := h.1
    have h2 : b ≤ min y y' := h.2
    rw [min_le_iff] at h1
    rw [le_min_iff] at h2
    cases h1 with
    | inl hxa => exact hxy ⟨hxa, h2.1⟩
    | inr hx'a => exact hx'y' ⟨hx'a, h2.2⟩
  · intro h
    have h1 : max x x' ≤ a := h.1
    have h2 : b ≤ max y y' := h.2
    rw [max_le_iff] at h1
    rw [le_max_iff] at h2
    cases h2 with
    | inl hby => exact hxy ⟨h1.1, hby⟩
    | inr hby' => exact hx'y' ⟨h1.2, hby'⟩
end P2MHole03_c5d429c1

/-- The relation `Holds (.nw a b) : ¬(x ≤ a ∧ b ≤ y)` is closed under coordinatewise
min and max: two points satisfying it imply their coordinatewise min and max do. -/
theorem nw_holds_minmax (a b x y x' y' : ℕ)
    (hxy : (Quadrant.nw a b).Holds x y) (hx'y' : (Quadrant.nw a b).Holds x' y') :
    (Quadrant.nw a b).Holds (min x x') (min y y') ∧
    (Quadrant.nw a b).Holds (max x x') (max y y') := by
  (first | exact P2MHole03_c5d429c1.solution a b x y x' y' hxy hx'y' | (apply P2MHole03_c5d429c1.solution <;> assumption))

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.3: every window `W_ij` is closed under coordinatewise
minimum and maximum. -/
theorem solution (Q : Finset Quadrant) (di dj : ℕ)
    (hQ : ∀ c ∈ Q, c.WellRanged di dj) :
    MinMaxClosed (window Q di dj) := by
  unfold MinMaxClosed
  intro x hx y hy
  rcases x with ⟨p, q⟩
  rcases y with ⟨p', q'⟩
  simp only [window, Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨h1p, hpdi, h1q, hdjq, hall⟩ := hx
  obtain ⟨h1p', hpdi', h1q', hdjq', hall'⟩ := hy
  obtain ⟨hboxm, hboxM⟩ :=
    box_minmax p q p' q' di dj ⟨h1p, hpdi, h1q, hdjq⟩ ⟨h1p', hpdi', h1q', hdjq'⟩
  constructor
  · refine ⟨hboxm.1, hboxm.2.1, hboxm.2.2.1, hboxm.2.2.2, ?_⟩
    intro c hc
    match c with
    | .se a b => exact (se_holds_minmax a b p q p' q' (hall (.se a b) hc) (hall' (.se a b) hc)).1
    | .nw a b => exact (nw_holds_minmax a b p q p' q' (hall (.nw a b) hc) (hall' (.nw a b) hc)).1
  · refine ⟨hboxM.1, hboxM.2.1, hboxM.2.2.1, hboxM.2.2.2, ?_⟩
    intro c hc
    match c with
    | .se a b => exact (se_holds_minmax a b p q p' q' (hall (.se a b) hc) (hall' (.se a b) hc)).2
    | .nw a b => exact (nw_holds_minmax a b p q p' q' (hall (.nw a b) hc) (hall' (.nw a b) hc)).2
