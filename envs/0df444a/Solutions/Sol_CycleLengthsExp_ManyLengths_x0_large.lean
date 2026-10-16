-- Prove2me | solution 1 for CycleLengthsExp.ManyLengths.x0_large
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-15T17:47:35.865354+00:00
-- url     : https://prove2.me/submissions/9a3da608-a3ab-4323-95e6-4a38fd9ed44f

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

set_option autoImplicit false

open SimpleGraph

/-- Ball of radius `r` around `Seed` by walks. -/
@[reducible]
def walkBall {V : Type*} (G : SimpleGraph V) (Seed : Set V) (r : ℕ) : Set V :=
  {w | ∃ s ∈ Seed, ∃ q : G.Walk s w, q.length ≤ r}

/-- `dropLast` commutes with `map`. -/
theorem List.dropLast_map' {V W : Type*} (f : V → W) (l : List V) :
    (l.map f).dropLast = (l.dropLast).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l' =>
      simp [List.dropLast_cons_cons]

/-- `tail` commutes with `map`. -/
theorem List.tail_map' {V W : Type*} (f : V → W) (l : List V) :
    (l.map f).tail = (l.tail).map f := by
  cases l with
  | nil => rfl
  | cons a l => rfl

/-- `tail` + `dropLast` commute with `map`. -/
theorem List.tail_dropLast_map {V W : Type*} (f : V → W) (l : List V) :
    (l.map f).tail.dropLast = (l.tail.dropLast).map f := by
  rw [List.tail_map', List.dropLast_map']

/-- A vertex in the tail of a path's support is not the start vertex. -/
theorem walk_mem_tail_ne_start {V : Type*} {G : SimpleGraph V} {s y : V} {q : G.Walk s y}
    (hq : q.IsPath) {z : V} (hz : z ∈ q.support.tail) : z ≠ s := by
  cases q with
  | nil => simp at hz
  | cons h q' =>
    rw [Walk.support_cons, List.tail_cons] at hz
    have hnod : (Walk.cons h q').support.Nodup := (Walk.isPath_def _).mp hq
    rw [Walk.support_cons] at hnod
    exact fun hze => (List.nodup_cons.mp hnod).1 (hze ▸ hz)

/-- A vertex in the `dropLast` of a path's support is not the end vertex. -/
theorem walk_mem_dropLast_ne_end {V : Type*} {G : SimpleGraph V} {s y : V} {q : G.Walk s y}
    (hq : q.IsPath) {z : V} (hz : z ∈ q.support.dropLast) : z ≠ y := by
  intro hze
  have hne : q.support ≠ [] := q.support_ne_nil
  have hgetLast : q.support.getLast hne = y := by
    have h1 : q.support.length - 1 = q.length := by
      rw [Walk.length_support]
      omega
    have h2 : q.support[q.support.length - 1] = y := by
      have hlt : q.support.length - 1 ≤ q.length := by
        have hls := Walk.length_support q
        omega
      have hget : q.getVert (q.support.length - 1) = y := by
        rw [h1]
        exact Walk.getVert_length q
      exact (Walk.getVert_eq_support_getElem q hlt).symm.trans hget
    rw [List.getLast_eq_getElem]
    exact h2
  have h1 : q.support.dropLast ++ [q.support.getLast hne] = q.support :=
    List.dropLast_append_getLast hne
  have hnod : (q.support.dropLast ++ [q.support.getLast hne]).Nodup := by
    rw [List.dropLast_append_getLast]
    exact (Walk.isPath_def _).mp hq
  have h3 : z ≠ q.support.getLast hne :=
    (List.nodup_append.mp hnod).2.2 z hz _ (List.mem_singleton_self _)
  rw [hgetLast] at h3
  exact h3 hze

open CycleLengthsExp.ManyLengths in
theorem solution (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (u v : Fin n) (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hdisj : ∀ w ∈ p.support, w ∉ S) :
    α ^ 2 * (n : ℝ) / 12 ≤ ((X0 α G S p).ncard : ℝ) := by
  classical
  set X0 : Set (Fin n) := CycleLengthsExp.ManyLengths.X0 α G S p with hX0def
  set G' := G.induce X0ᶜ with hG'def
  set m : ℕ := Nat.ceil (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) with hm_def
  set Pset : Set (Fin n) := ↑p.support.toFinset with hPsetdef
  set S' : Set ↥X0ᶜ := {w | (w : Fin n) ∈ S} with hS'def
  set P' : Set ↥X0ᶜ := {w | (w : Fin n) ∈ Pset} with hP'def
  -- Basic real facts.
  have hαn_pos : (0 : ℝ) < α * (n : ℝ) := by linarith
  have hαn_le : α * (n : ℝ) ≤ (n : ℝ) := by
    calc α * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hα1 (by positivity)
      _ = (n : ℝ) := one_mul _
  have hnR : (12 : ℝ) ≤ (n : ℝ) := le_trans hn hαn_le
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hlog : (0 : ℝ) < Real.logb 2 (1 + α / 2) :=
    Real.logb_pos (by norm_num) (by linarith)
  -- `(1 + α/2)^m ≥ 3/α` from the definition of `m`.
  have hpow : (3 / α) ≤ (1 + α / 2) ^ m := by
    have h1 : Real.logb 2 (3 / α) ≤ (m : ℝ) * Real.logb 2 (1 + α / 2) := by
      have h2 : Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2) ≤ (m : ℝ) := by
        rw [hm_def]
        exact Nat.le_ceil _
      have h3 : Real.logb 2 (3 / α) =
          (Real.logb 2 (3 / α) / Real.logb 2 (1 + α / 2)) *
            Real.logb 2 (1 + α / 2) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hlog)]
      rw [h3]
      exact mul_le_mul_of_nonneg_right h2 (le_of_lt hlog)
    have hle : Real.logb 2 (3 / α) ≤ Real.logb 2 ((1 + α / 2) ^ m) := by
      rw [Real.logb_pow]
      exact h1
    exact (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mp hle
  -- `|S| > αn/6`.
  have hS_gt : (α * (n : ℝ) / 6) < (S.ncard : ℝ) := by
    have h1 : (S.ncard : ℝ) > α * (n : ℝ) / 4 - 1 := by
      rw [hS]
      have h2 := Nat.lt_floor_add_one (α * (n : ℝ) / 4)
      linarith
    have h2 : (1 : ℝ) ≤ α * (n : ℝ) / 12 := by linarith
    linarith
  -- `|P| = ⌈αn/4⌉`.
  have hPcard : (Pset.ncard : ℝ) = (Nat.ceil (α * (n : ℝ) / 4) : ℝ) := by
    have ncard_coe : ∀ (s : Finset (Fin n)), (↑s : Set (Fin n)).ncard = s.card := by
      intro s
      show ENat.toNat (↑s : Set (Fin n)).encard = s.card
      rw [Set.encard_coe_eq_coe_finsetCard]
      simp
    have hceil_pos : 1 ≤ Nat.ceil (α * (n : ℝ) / 4) :=
      Nat.ceil_pos.mpr (by positivity)
    have h1 : Pset.ncard = Nat.ceil (α * (n : ℝ) / 4) := by
      rw [hPsetdef, ncard_coe, List.toFinset_card_of_nodup ((Walk.isPath_def _).mp hp),
        Walk.length_support, hlen]
      omega
    rw [h1]
  -- `X0 ⊆ P`.
  have hX0sub : X0 ⊆ Pset := by
    intro x hx
    rw [hX0def] at hx
    obtain ⟨hxP, -⟩ := hx
    rw [hPsetdef, Finset.mem_coe, List.mem_toFinset]
    exact hxP
  have hdisj' : ∀ w ∈ Pset, w ∉ S := by
    intro w hw hwS
    rw [hPsetdef, Finset.mem_coe, List.mem_toFinset] at hw
    exact hdisj w hw hwS
  by_contra hcon
  have hlt : (X0.ncard : ℝ) < α ^ 2 * (n : ℝ) / 12 := lt_of_not_ge hcon
  -- Expansion in `G' = G - X0`: for `|U|` between `αn/6` and `n/2`,
  -- `|N_{G'}(U)| ≥ (α/2)|U|`.
  have hexp' : ∀ U : Set ↥X0ᶜ, (α * (n : ℝ) / 6) ≤ (U.ncard : ℝ) →
      (U.ncard : ℝ) ≤ (n : ℝ) / 2 →
      (α / 2) * (U.ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G' U).ncard : ℝ) := by
    intro U hUlo hUhi
    set U0 : Set (Fin n) := Subtype.val '' U with hU0def
    have hU0card : (U0.ncard : ℝ) = (U.ncard : ℝ) := by
      rw [hU0def, Set.ncard_image_of_injective _ Subtype.val_injective]
    have himg : Subtype.val '' (CycleLengthsExp.WellSpread.extNbhd G' U) =
        CycleLengthsExp.WellSpread.extNbhd G U0 \ X0 := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := hz
        obtain ⟨hwU, u, huU, hadj⟩ := hw
        refine ⟨⟨?_, ⟨(u : Fin n), ⟨u, huU, rfl⟩, hadj⟩⟩, w.2⟩
        intro hzU0
        obtain ⟨u', hu'U, hu'eq⟩ := hzU0
        exact hwU (by have h : u' = w := Subtype.ext hu'eq; rw [h] at hu'U; exact hu'U)
      · intro hz
        obtain ⟨⟨hzU0, u0, hu0U0, hadj⟩, hzX0⟩ := hz
        obtain ⟨u, huU, hu0eq⟩ := hu0U0
        refine ⟨⟨z, hzX0⟩, ⟨?_, u, huU, ?_⟩, rfl⟩
        · intro hmem
          exact hzU0 ⟨⟨z, hzX0⟩, hmem, rfl⟩
        · have hadj' : G.Adj (u : Fin n) z := by
            rw [hu0eq]
            exact hadj
          exact hadj'
    have hcard1 : ((CycleLengthsExp.WellSpread.extNbhd G' U).ncard : ℝ) =
        ((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0).ncard : ℝ) := by
      rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]
    have hge : ((CycleLengthsExp.WellSpread.extNbhd G U0).ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0).ncard : ℝ) +
          (X0.ncard : ℝ) := by
      have hsub : CycleLengthsExp.WellSpread.extNbhd G U0 ⊆
          (CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) ∪ X0 := by
        intro z hz
        by_cases hzX : z ∈ X0
        · exact Or.inr hzX
        · exact Or.inl ⟨hz, hzX⟩
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_union_le (CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) X0
      have h1' : ((CycleLengthsExp.WellSpread.extNbhd G U0).ncard : ℝ) ≤
          (((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) ∪ X0).ncard : ℝ) := by
        exact_mod_cast h1
      have h2' : (((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0) ∪ X0).ncard : ℝ) ≤
          ((CycleLengthsExp.WellSpread.extNbhd G U0 \ X0).ncard : ℝ) +
            (X0.ncard : ℝ) := by
        exact_mod_cast h2
      linarith
    have hexpG : α * (U0.ncard : ℝ) ≤
        ((CycleLengthsExp.WellSpread.extNbhd G U0).ncard : ℝ) := by
      have hU0le : U0.ncard ≤ (Fintype.card (Fin n) + 1) / 2 := by
        rw [Fintype.card_fin]
        have h1 : U0.ncard ≤ n / 2 := by
          by_contra hcon1
          have h4 : n / 2 + 1 ≤ U0.ncard := by omega
          have h5 : ((n / 2 + 1 : ℕ) : ℝ) ≤ (U0.ncard : ℝ) := by exact_mod_cast h4
          have h6 : (n : ℝ) / 2 < ((n / 2 + 1 : ℕ) : ℝ) := by
            have h7 : n < 2 * (n / 2 + 1) := by omega
            have h8 : (n : ℝ) < 2 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h7
            linarith
          have h2 : (U0.ncard : ℝ) ≤ (n : ℝ) / 2 := by
            rw [hU0card]
            exact hUhi
          linarith
        omega
      exact hG U0 hU0le
    rw [hU0card] at hexpG
    have hαU : α ^ 2 * (n : ℝ) / 12 ≤ (α / 2) * (U.ncard : ℝ) := by
      have h1 : (α / 2) * (α * (n : ℝ) / 6) = α ^ 2 * (n : ℝ) / 12 := by
        field_simp
        ring
      rw [← h1]
      exact mul_le_mul_of_nonneg_left hUlo (by linarith : (0 : ℝ) ≤ α / 2)
    have hhalf : (α / 2) * (U.ncard : ℝ) =
        α * (U.ncard : ℝ) - (α / 2) * (U.ncard : ℝ) := by ring
    rw [hcard1]
    linarith [hge, hexpG, hαU, hlt, hU0card, hhalf]
  -- Ball growth in `G'`: either the ball exceeds `n/2`, or it grows by `(1 + α/2)`
  -- at each step.
  have hball : ∀ (Seed : Set ↥X0ᶜ), (α * (n : ℝ) / 6) ≤ (Seed.ncard : ℝ) →
      ∀ r : ℕ, ((n : ℝ) / 2 < ((walkBall G' Seed r).ncard : ℝ)) ∨
        ((1 + α / 2) ^ r * (Seed.ncard : ℝ) ≤ ((walkBall G' Seed r).ncard : ℝ)) := by
    intro Seed hSeed r
    induction r with
    | zero =>
      right
      have hB0 : walkBall G' Seed 0 = Seed := by
        ext w
        constructor
        · intro hw
          obtain ⟨s, hs, q, hq⟩ := hw
          have hq0 : q.length = 0 := Nat.le_zero.mp hq
          cases q with
          | nil => exact hs
          | cons h' q'' => simp [Walk.length_cons] at hq0
        · intro hw
          exact ⟨w, hw, Walk.nil, by simp⟩
      rw [hB0]
      simp
    | succ r ih =>
      rcases ih with h | h
      · left
        have hmono : walkBall G' Seed r ⊆ walkBall G' Seed (r + 1) := by
          intro w hw
          obtain ⟨s, hs, q, hq⟩ := hw
          exact ⟨s, hs, q, le_trans hq (Nat.le_succ r)⟩
        have hle := Set.ncard_le_ncard hmono (Set.toFinite _)
        exact lt_of_lt_of_le h (by exact_mod_cast hle)
      · by_cases hbig : (n : ℝ) / 2 < ((walkBall G' Seed r).ncard : ℝ)
        · left
          have hmono : walkBall G' Seed r ⊆ walkBall G' Seed (r + 1) := by
            intro w hw
            obtain ⟨s, hs, q, hq⟩ := hw
            exact ⟨s, hs, q, le_trans hq (Nat.le_succ r)⟩
          have hle := Set.ncard_le_ncard hmono (Set.toFinite _)
          exact lt_of_lt_of_le hbig (by exact_mod_cast hle)
        · have hBlo : (α * (n : ℝ) / 6) ≤ ((walkBall G' Seed r).ncard : ℝ) := by
            have h1 : (1 : ℝ) ≤ (1 + α / 2) ^ r := one_le_pow₀ (by linarith)
            have h2 : (1 : ℝ) * (Seed.ncard : ℝ) ≤
                (1 + α / 2) ^ r * (Seed.ncard : ℝ) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            rw [one_mul] at h2
            linarith [h, h2, hSeed]
          have hBhi : ((walkBall G' Seed r).ncard : ℝ) ≤ (n : ℝ) / 2 :=
            le_of_not_gt hbig
          have hexp := hexp' _ hBlo hBhi
          have hsub : walkBall G' Seed r ∪
              CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r) ⊆
              walkBall G' Seed (r + 1) := by
            intro w hw
            rcases hw with hw | hw
            · obtain ⟨s, hs, q, hq⟩ := hw
              exact ⟨s, hs, q, le_trans hq (Nat.le_succ r)⟩
            · obtain ⟨hwU, u, hu, hadj⟩ := hw
              obtain ⟨s, hs, q, hq⟩ := hu
              exact ⟨s, hs, q.concat hadj, by rw [Walk.length_concat]; omega⟩
          have hdisj : Disjoint (walkBall G' Seed r)
              (CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)) := by
            rw [Set.disjoint_left]
            intro w hw hw2
            obtain ⟨hw2a, -⟩ := hw2
            exact hw2a hw
          have hcard : ((walkBall G' Seed r).ncard : ℝ) +
              ((CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) ≤
              ((walkBall G' Seed (r + 1)).ncard : ℝ) := by
            have h1 : ((walkBall G' Seed r ∪
                CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) =
                ((walkBall G' Seed r).ncard : ℝ) +
                  ((CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) := by
              have h := Set.ncard_union_eq hdisj
              exact_mod_cast h
            have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
            have h2' : ((walkBall G' Seed r ∪
                CycleLengthsExp.WellSpread.extNbhd G' (walkBall G' Seed r)).ncard : ℝ) ≤
                ((walkBall G' Seed (r + 1)).ncard : ℝ) := by
              exact_mod_cast h2
            linarith [h1, h2']
          right
          have hgrow : (1 + α / 2) ^ (r + 1) * (Seed.ncard : ℝ) ≤
              (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) := by
            have hmul := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 + α / 2)
            calc (1 + α / 2) ^ (r + 1) * (Seed.ncard : ℝ)
                = (1 + α / 2) * ((1 + α / 2) ^ r * (Seed.ncard : ℝ)) := by
                  rw [pow_succ]
                  ring
              _ ≤ (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) := hmul
          have hfinal : (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) ≤
              ((walkBall G' Seed (r + 1)).ncard : ℝ) := by
            have e : (1 + α / 2) * ((walkBall G' Seed r).ncard : ℝ) =
                ((walkBall G' Seed r).ncard : ℝ) +
                  (α / 2) * ((walkBall G' Seed r).ncard : ℝ) := by ring
            rw [e]
            linarith [hcard, hexp]
          exact le_trans hgrow hfinal
  -- `|S'| = |S|`.
  have hS'card : (S'.ncard : ℝ) = (S.ncard : ℝ) := by
    have himg : Subtype.val '' S' = S := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hz
        have hzX : z ∉ X0 := fun h => hdisj' z (hX0sub h) hz
        exact ⟨⟨z, hzX⟩, hz, rfl⟩
    have h := Set.ncard_image_of_injective S' Subtype.val_injective
    rw [himg] at h
    exact_mod_cast h.symm
  -- `|P'| > αn/6`.
  have hP'card : (P'.ncard : ℝ) > α * (n : ℝ) / 6 := by
    have himg : Subtype.val '' P' = Pset \ X0 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.2⟩
      · rintro ⟨hzP, hzX⟩
        exact ⟨⟨z, hzX⟩, hzP, rfl⟩
    have h1 : (P'.ncard : ℝ) = ((Pset \ X0).ncard : ℝ) := by
      have h := Set.ncard_image_of_injective P' Subtype.val_injective
      rw [himg] at h
      exact_mod_cast h.symm
    have h2 : (Pset.ncard : ℝ) ≤ ((Pset \ X0).ncard : ℝ) + (X0.ncard : ℝ) := by
      have hsub : Pset ⊆ (Pset \ X0) ∪ X0 := by
        intro z hz
        by_cases hzX : z ∈ X0
        · exact Or.inr hzX
        · exact Or.inl ⟨hz, hzX⟩
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h4 := Set.ncard_union_le (Pset \ X0) X0
      have h3' : (Pset.ncard : ℝ) ≤ (((Pset \ X0) ∪ X0).ncard : ℝ) := by
        exact_mod_cast h3
      have h4' : (((Pset \ X0) ∪ X0).ncard : ℝ) ≤
          ((Pset \ X0).ncard : ℝ) + (X0.ncard : ℝ) := by
        exact_mod_cast h4
      linarith
    have h3 : α ^ 2 * (n : ℝ) ≤ α * (n : ℝ) := by
      calc α ^ 2 * (n : ℝ) = α * (α * (n : ℝ)) := by ring
        _ ≤ 1 * (α * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hα1 (by positivity)
        _ = α * (n : ℝ) := one_mul _
    have hP4 : (α * (n : ℝ) / 4) ≤ (Pset.ncard : ℝ) := by
      rw [hPcard]
      exact Nat.le_ceil _
    rw [h1]
    linarith [h2, hP4, hlt, h3]
  -- Both balls at radius `m` exceed `n/2`.
  have hBS : (n : ℝ) / 2 < ((walkBall G' S' m).ncard : ℝ) := by
    rcases hball S' (by rw [hS'card]; exact le_of_lt hS_gt) m with h | h
    · exact h
    · have h1 : (3 / α) * (α * (n : ℝ) / 6) <
          (1 + α / 2) ^ m * (S'.ncard : ℝ) := by
        have h2 : (3 / α) * (α * (n : ℝ) / 6) < (3 / α) * (S'.ncard : ℝ) :=
          mul_lt_mul_of_pos_left (by rw [hS'card]; exact hS_gt) (by positivity)
        have h3 : (3 / α) * (S'.ncard : ℝ) ≤
            (1 + α / 2) ^ m * (S'.ncard : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
        linarith
      have h4 : (3 / α) * (α * (n : ℝ) / 6) = (n : ℝ) / 2 := by
        field_simp
        ring
      linarith [h, h1, h4]
  have hBP : (n : ℝ) / 2 < ((walkBall G' P' m).ncard : ℝ) := by
    rcases hball P' (le_of_lt hP'card) m with h | h
    · exact h
    · have h1 : (3 / α) * (α * (n : ℝ) / 6) <
          (1 + α / 2) ^ m * (P'.ncard : ℝ) := by
        have h2 : (3 / α) * (α * (n : ℝ) / 6) < (3 / α) * (P'.ncard : ℝ) :=
          mul_lt_mul_of_pos_left hP'card (by positivity)
        have h3 : (3 / α) * (P'.ncard : ℝ) ≤
            (1 + α / 2) ^ m * (P'.ncard : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
        linarith
      have h4 : (3 / α) * (α * (n : ℝ) / 6) = (n : ℝ) / 2 := by
        field_simp
        ring
      linarith [h, h1, h4]
  -- The two balls intersect.
  obtain ⟨w, hwS, hwP⟩ : ∃ w, w ∈ walkBall G' S' m ∧ w ∈ walkBall G' P' m := by
    by_contra hcon2
    have hcon2' : ∀ w, w ∈ walkBall G' S' m → w ∉ walkBall G' P' m := by
      intro w hw hw2
      exact hcon2 ⟨w, hw, hw2⟩
    have hdisj : Disjoint (walkBall G' S' m) (walkBall G' P' m) := by
      rw [Set.disjoint_left]
      intro x hx hx2
      exact hcon2' x hx hx2
    have hunion : ((walkBall G' S' m ∪ walkBall G' P' m).ncard : ℝ) =
        ((walkBall G' S' m).ncard : ℝ) + ((walkBall G' P' m).ncard : ℝ) := by
      have h := Set.ncard_union_eq hdisj
      exact_mod_cast h
    have hle : ((walkBall G' S' m ∪ walkBall G' P' m).ncard : ℝ) ≤ (n : ℝ) := by
      have h1 := Set.ncard_le_ncard
        (Set.subset_univ (walkBall G' S' m ∪ walkBall G' P' m))
      have h2 : ((Set.univ : Set ↥X0ᶜ).ncard : ℝ) ≤ (n : ℝ) := by
        have h3 : (Set.univ : Set ↥X0ᶜ).ncard = (X0ᶜ).ncard := by
          rw [Set.ncard_univ, Nat.card_coe_set_eq]
        have h4 : (X0ᶜ).ncard = n - X0.ncard := by
          rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
        rw [h3, h4]
        have h5 : X0.ncard ≤ n := by
          have h6 : X0.ncard ≤ Pset.ncard := Set.ncard_le_ncard hX0sub (Set.toFinite _)
          have h7 : Pset.ncard ≤ n := by
            have h8 := Set.ncard_le_ncard (Set.subset_univ Pset) (Set.toFinite _)
            rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h8
          omega
        have h6 : ((n - X0.ncard : ℕ) : ℝ) ≤ (n : ℝ) := by
          rw [Nat.cast_sub h5]
          have h7 : (0 : ℝ) ≤ (X0.ncard : ℝ) := by positivity
          linarith
        exact h6
      have h1' : ((walkBall G' S' m ∪ walkBall G' P' m).ncard : ℝ) ≤
          ((Set.univ : Set ↥X0ᶜ).ncard : ℝ) := by
        exact_mod_cast h1
      linarith
    linarith [hBS, hBP, hunion, hle]
  -- A walk from `S` to `P` in `G'` of length at most `2m`.
  obtain ⟨s₀, hs₀, q₁, hq₁⟩ := hwS
  obtain ⟨y₀, hy₀, q₂, hq₂⟩ := hwP
  obtain ⟨qpath, hqpath, hqplen⟩ :
      ∃ q : G'.Walk s₀ y₀, q.IsPath ∧ q.length ≤ 2 * m := by
    have hwalk : ∃ q : G'.Walk s₀ y₀, q.length ≤ 2 * m := by
      refine ⟨q₁.append q₂.reverse, ?_⟩
      rw [Walk.length_append, Walk.length_reverse]
      omega
    obtain ⟨q, hq⟩ := hwalk
    exact ⟨(q.toPath : G'.Walk s₀ y₀), q.toPath.isPath,
      le_trans q.length_bypass_le_length hq⟩
  -- A shortest path from `S` to `P` in `G'`.
  have hTne : ∃ ℓ, ∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
      ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
        ∃ q : G'.Walk s₀ y₀, q.IsPath ∧ q.length = ℓ :=
    ⟨qpath.length, s₀, hs₀, y₀, hy₀, qpath, hqpath, rfl⟩
  set ℓstar := Nat.find hTne with hℓdef
  have hspec := Nat.find_spec hTne
  obtain ⟨s₁, hs₁, y₁, hy₁, q, hqpathMin, hqlen⟩ := hspec
  have hmin : ∀ ℓ, (∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
      ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
        ∃ q : G'.Walk s₀ y₀, q.IsPath ∧ q.length = ℓ) → ℓstar ≤ ℓ :=
    fun ℓ hℓ => Nat.find_min' hTne hℓ
  have hℓle : ℓstar ≤ 2 * m := by
    have h1 : ℓstar ≤ qpath.length :=
      hmin _ ⟨s₀, hs₀, y₀, hy₀, qpath, hqpath, rfl⟩
    exact le_trans h1 hqplen
  have hkNum : CycleLengthsExp.ManyLengths.kNum α = 2 * m + 1 := rfl
  -- Internal vertices of the shortest path avoid `S` (else the suffix is shorter).
  have hAvoidS : ∀ j, 0 < j → j < q.length → (q.getVert j : Fin n) ∉ S := by
    intro j hj0 hjlen hmem
    have hmemT : ∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
        ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
          ∃ q' : G'.Walk s₀ y₀, q'.IsPath ∧ q'.length = (q.drop j).length :=
      ⟨q.getVert j, hmem, y₁, hy₁, q.drop j, hqpathMin.drop j, rfl⟩
    have hle := hmin _ hmemT
    rw [Walk.drop_length] at hle
    omega
  -- Internal vertices avoid `P` (else the prefix is shorter).
  have hAvoidP : ∀ j, 0 < j → j < q.length → (q.getVert j : Fin n) ∉ Pset := by
    intro j hj0 hjlen hmem
    have hmemT : ∃ (s₀ : ↥X0ᶜ), (s₀ : Fin n) ∈ S ∧
        ∃ (y₀ : ↥X0ᶜ), (y₀ : Fin n) ∈ Pset ∧
          ∃ q' : G'.Walk s₀ y₀, q'.IsPath ∧ q'.length = (q.take j).length :=
      ⟨s₁, hs₁, q.getVert j, hmem, q.take j, hqpathMin.take j, rfl⟩
    have hle := hmin _ hmemT
    rw [Walk.take_length] at hle
    omega
  -- The endpoint `y₁` lies in `X0`: contradiction with `y₁ ∉ X0`.
  have hy1X0 : (y₁ : Fin n) ∈ X0 := by
    refine ⟨?_, ⟨(s₁ : Fin n), hs₁, q.map ⟨Subtype.val, fun h => h⟩, ?_, ?_, ?_⟩⟩
    · have h : (y₁ : Fin n) ∈ Pset := hy₁
      rw [hPsetdef] at h
      exact List.mem_toFinset.mp (Finset.mem_coe.mp h)
    · exact (Walk.isPath_map_iff_of_injective
        (f := (⟨Subtype.val, fun h => h⟩ : G' →g G)) Subtype.val_injective).mpr hqpathMin
    · rw [Walk.length_map, hqlen, hkNum]
      omega
    · intro y hy
      rw [Walk.support_map, List.tail_map', List.dropLast_map'] at hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      show (z : Fin n) ∉ S ∧ (z : Fin n) ∉ p.support
      have hzTail : z ∈ q.support.tail := List.mem_of_mem_dropLast hz
      have hzDrop : z ∈ q.support.dropLast := by
        have hsub : q.support.tail.dropLast ⊆ q.support.dropLast := by
          cases hsup : q.support with
          | nil => simp
          | cons a l =>
            cases l with
            | nil => simp
            | cons b l' =>
              intro w hw
              simp only [List.tail_cons] at hw
              rw [List.dropLast_cons_cons]
              exact List.mem_cons_of_mem a hw
        exact hsub hz
      have hzne : z ≠ s₁ := walk_mem_tail_ne_start hqpathMin hzTail
      have hzne2 : z ≠ y₁ := walk_mem_dropLast_ne_end hqpathMin hzDrop
      obtain ⟨j, hjEq, hjle⟩ := Walk.mem_support_iff_exists_getVert.mp
        (List.mem_of_mem_tail hzTail)
      have hj0 : 0 < j := by
        by_contra hcon0
        have hj0' : j = 0 := by omega
        rw [hj0', Walk.getVert_zero] at hjEq
        exact hzne hjEq.symm
      have hjlt : j < q.length := by
        by_contra hcon0
        have hjeq : j = q.length := by omega
        rw [hjeq, Walk.getVert_length] at hjEq
        exact hzne2 hjEq.symm
      have h1 := hAvoidS j hj0 hjlt
      have h2 := hAvoidP j hj0 hjlt
      rw [hjEq] at h1 h2
      constructor
      · exact h1
      · intro hmem
        exact h2 (by rw [hPsetdef]; exact Finset.mem_coe.mpr (List.mem_toFinset.mpr hmem))
  exact y₁.2 hy1X0

namespace CycleLengthsExp.ManyLengths

theorem x0_large (n : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hn : 12 ≤ α * (n : ℝ)) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4))
    (u v : Fin n) (p : G.Walk u v) (hp : p.IsPath)
    (hlen : p.length = Nat.ceil (α * (n : ℝ) / 4) - 1)
    (hdisj : ∀ w ∈ p.support, w ∉ S) :
    α ^ 2 * (n : ℝ) / 12 ≤ ((X0 α G S p).ncard : ℝ) :=
  solution n α hα hα1 hn G hG S hS u v p hp hlen hdisj

end CycleLengthsExp.ManyLengths
