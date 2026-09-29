-- Prove2me | solution 2 for BrinSquier.supp_finite_components
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T19:19:00.184987+00:00
-- url     : https://prove2.me/submissions/fd2af307-d9e7-4d79-b3d8-0c5dcc2c28b6

import Theorems.Thm_TopCover_finite_components_of_finite_cover
import Definitions.Def_BrinSquier
import Mathlib

namespace BS_all
open BrinSquier

variable (B : Finset ℝ)

/-- The open gap immediately to the left of `b`: everything below `b` that is above every
element of `B` lying below `b`. No sorting required. -/
def gapBelow (b : ℝ) : Set ℝ := {y | y < b ∧ ∀ c ∈ B, y ≤ c → b ≤ c}

/-- The unbounded gap above every element of `B`. -/
def gapTop : Set ℝ := {y | ∀ c ∈ B, c < y}

lemma gapBelow_ordConnected (b : ℝ) : (gapBelow B b).OrdConnected := by
  constructor
  intro y hy z hz w hw
  refine ⟨lt_of_le_of_lt hw.2 hz.1, fun c hc hyc => ?_⟩
  exact hy.2 c hc (le_trans hw.1 hyc)

lemma gapTop_ordConnected : (gapTop B).OrdConnected := by
  constructor
  intro y hy z hz w hw
  exact fun c hc => lt_of_lt_of_le (hy c hc) hw.1

lemma gapBelow_disj (b : ℝ) : ∀ y ∈ gapBelow B b, y ∉ (B : Set ℝ) := by
  intro y hy hmem
  exact absurd (hy.2 y (Finset.mem_coe.mp hmem) le_rfl) (not_le.mpr hy.1)

lemma gapTop_disj : ∀ y ∈ gapTop B, y ∉ (B : Set ℝ) := by
  intro y hy hmem
  exact absurd (hy y (Finset.mem_coe.mp hmem)) (lt_irrefl y)

/-- The gaps together with the points of `B` cover the line. -/
lemma gaps_cover (y : ℝ) :
    y ∈ (B : Set ℝ) ∨ y ∈ gapTop B ∨ ∃ b ∈ B, y ∈ gapBelow B b := by
  classical
  by_cases hyB : y ∈ (B : Set ℝ)
  · exact Or.inl hyB
  by_cases htop : ∀ c ∈ B, c < y
  · exact Or.inr (Or.inl htop)
  · push_neg at htop
    obtain ⟨c₀, hc₀B, hc₀⟩ := htop
    -- the least element of `B` strictly above `y`
    set S := B.filter (fun c => y < c) with hS
    have hSne : S.Nonempty := by
      refine ⟨c₀, ?_⟩
      rw [hS, Finset.mem_filter]
      refine ⟨hc₀B, lt_of_le_of_ne hc₀ ?_⟩
      intro h; exact hyB (by rw [h]; exact Finset.mem_coe.mpr hc₀B)
    set b := S.min' hSne with hb
    have hbS : b ∈ S := S.min'_mem hSne
    rw [hS, Finset.mem_filter] at hbS
    refine Or.inr (Or.inr ⟨b, hbS.1, hbS.2, fun c hc hyc => ?_⟩)
    by_contra hlt
    push_neg at hlt
    have : c ∈ S := by
      rw [hS, Finset.mem_filter]
      refine ⟨hc, lt_of_le_of_ne hyc ?_⟩
      intro h; exact hyB (by rw [h]; exact Finset.mem_coe.mpr hc)
    exact absurd (S.min'_le c this) (not_le.mpr hlt)

lemma affine_unique {a b a' b' y₁ y₂ : ℝ} (hne : y₁ ≠ y₂)
    (h1 : a * y₁ + b = a' * y₁ + b') (h2 : a * y₂ + b = a' * y₂ + b') :
    a = a' ∧ b = b' := by
  have hsub : (a - a') * (y₁ - y₂) = 0 := by nlinarith [h1, h2]
  have haa : a - a' = 0 := by
    rcases mul_eq_zero.1 hsub with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hne
  have ha : a = a' := by linarith
  refine ⟨ha, ?_⟩
  rw [ha] at h1
  linarith

/-- Local affineness on an open interval makes `f` affine on the whole interval. -/
theorem affine_on_Ioo {f : ℝ → ℝ} {p q : ℝ}
    (H : ∀ x ∈ Set.Ioo p q, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo p q) :
    ∃ a b : ℝ, ∀ y ∈ Set.Ioo p q, f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  obtain ⟨hpx, hxq⟩ := hx₀
  refine ⟨a₀, b₀, ?_⟩
  -- LEFT: agreement on (p, x₀]
  have left : ∀ y ∈ Set.Ioc p x₀, f y = a₀ * y + b₀ := by
    set S : Set ℝ := {t : ℝ | p < t ∧ t ≤ x₀ ∧ ∀ z ∈ Set.Icc t x₀, f z = a₀ * z + b₀} with hS
    set t₁ := max ((p + x₀)/2) (x₀ - e₀/2) with ht₁
    have ht₁p : p < t₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have ht₁x : t₁ < x₀ := max_lt (by linarith) (by linarith)
    have ht₁e : x₀ - e₀/2 ≤ t₁ := le_max_right _ _
    have hbase : t₁ ∈ S :=
      ⟨ht₁p, le_of_lt ht₁x, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hne : S.Nonempty := ⟨_, hbase⟩
    have hbdd : BddBelow S := ⟨p, fun z hz => le_of_lt hz.1⟩
    have hcp : sInf S = p := by
      by_contra hcne
      have hge : p ≤ sInf S := le_csInf hne (fun z hz => le_of_lt hz.1)
      have hgt : p < sInf S := lt_of_le_of_ne hge (Ne.symm hcne)
      set c := sInf S with hc
      have hcx : c ≤ t₁ := csInf_le hbdd hbase
      have hcq : c < q := by linarith
      obtain ⟨e, he, a, b, h⟩ := H c ⟨hgt, hcq⟩
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne
        (show c < c + min e (x₀ - c) by
          have : 0 < min e (x₀ - c) := lt_min he (by linarith)
          linarith)
      have hct : c ≤ t := csInf_le hbdd htS
      have htx : t < x₀ := by have := min_le_right e (x₀ - c); linarith
      have hte : t < c + e := by have := min_le_left e (x₀ - c); linarith
      set u := min (c + e) x₀ with hu
      have htu : t < u := lt_min hte htx
      set pp := (t + u)/2 with hpp
      have htp : t < pp := by simp only [hpp]; linarith
      have hpu : pp < u := by simp only [hpp]; linarith
      have hpx2 : pp ≤ x₀ := le_of_lt (lt_of_lt_of_le hpu (min_le_right _ _))
      have hpe : pp < c + e := lt_of_lt_of_le hpu (min_le_left _ _)
      have e1 : f t = a₀ * t + b₀ := htS.2.2 t ⟨le_refl _, le_of_lt htx⟩
      have e2 : f pp = a₀ * pp + b₀ := htS.2.2 pp ⟨le_of_lt htp, hpx2⟩
      have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
      have e4 : f pp = a * pp + b := h pp ⟨by linarith, by linarith⟩
      obtain ⟨haa, hbb⟩ := affine_unique (ne_of_lt htp) (e3.symm.trans e1) (e4.symm.trans e2)
      set c' := max ((p + c)/2) (c - e/2) with hc'
      have hc'p : p < c' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hc'c : c' < c := max_lt (by linarith) (by linarith)
      have hc'e : c - e/2 ≤ c' := le_max_right _ _
      have : c' ∈ S := by
        refine ⟨hc'p, by linarith, fun z hz => ?_⟩
        by_cases hzt : t ≤ z
        · exact htS.2.2 z ⟨hzt, hz.2⟩
        · replace hzt := not_le.mp hzt
          have := h z ⟨by linarith [hz.1], by linarith⟩
          rw [this, haa, hbb]
      have := csInf_le hbdd this
      linarith
    intro y hy
    obtain ⟨t, htS, hty⟩ := exists_lt_of_csInf_lt hne (by rw [hcp]; exact hy.1)
    exact htS.2.2 y ⟨le_of_lt hty, hy.2⟩
  -- RIGHT: agreement on [x₀, q)
  have right : ∀ y ∈ Set.Ico x₀ q, f y = a₀ * y + b₀ := by
    set S : Set ℝ := {t : ℝ | t < q ∧ x₀ ≤ t ∧ ∀ z ∈ Set.Icc x₀ t, f z = a₀ * z + b₀} with hS
    set t₁ := min ((q + x₀)/2) (x₀ + e₀/2) with ht₁
    have ht₁q : t₁ < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₁x : x₀ < t₁ := lt_min (by linarith) (by linarith)
    have ht₁e : t₁ ≤ x₀ + e₀/2 := min_le_right _ _
    have hbase : t₁ ∈ S :=
      ⟨ht₁q, le_of_lt ht₁x, fun z hz => h₀ z ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    have hne : S.Nonempty := ⟨_, hbase⟩
    have hbdd : BddAbove S := ⟨q, fun z hz => le_of_lt hz.1⟩
    have hcq : sSup S = q := by
      by_contra hcne
      have hle : sSup S ≤ q := csSup_le hne (fun z hz => le_of_lt hz.1)
      have hlt : sSup S < q := lt_of_le_of_ne hle hcne
      set c := sSup S with hc
      have hcx : t₁ ≤ c := le_csSup hbdd hbase
      have hcp2 : p < c := by linarith
      obtain ⟨e, he, a, b, h⟩ := H c ⟨hcp2, hlt⟩
      obtain ⟨t, htS, htlt⟩ := exists_lt_of_lt_csSup hne
        (show c - min e (c - x₀) < c by
          have : 0 < min e (c - x₀) := lt_min he (by linarith)
          linarith)
      have hct : t ≤ c := le_csSup hbdd htS
      have htx : x₀ < t := by have := min_le_right e (c - x₀); linarith
      have hte : c - e < t := by have := min_le_left e (c - x₀); linarith
      set u := max (c - e) x₀ with hu
      have hut : u < t := max_lt hte htx
      set pp := (u + t)/2 with hpp
      have hpt : pp < t := by simp only [hpp]; linarith
      have hup : u < pp := by simp only [hpp]; linarith
      have hpx2 : x₀ ≤ pp := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hup)
      have hpe : c - e < pp := lt_of_le_of_lt (le_max_left _ _) hup
      have e1 : f t = a₀ * t + b₀ := htS.2.2 t ⟨le_of_lt htx, le_refl _⟩
      have e2 : f pp = a₀ * pp + b₀ := htS.2.2 pp ⟨hpx2, le_of_lt hpt⟩
      have e3 : f t = a * t + b := h t ⟨by linarith, by linarith⟩
      have e4 : f pp = a * pp + b := h pp ⟨by linarith, by linarith⟩
      obtain ⟨haa, hbb⟩ := affine_unique (ne_of_gt hpt) (e3.symm.trans e1) (e4.symm.trans e2)
      set c' := min ((q + c)/2) (c + e/2) with hc'
      have hc'q : c' < q := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hc'c : c < c' := lt_min (by linarith) (by linarith)
      have hc'e : c' ≤ c + e/2 := min_le_right _ _
      have : c' ∈ S := by
        refine ⟨hc'q, by linarith, fun z hz => ?_⟩
        by_cases hzt : z ≤ t
        · exact htS.2.2 z ⟨hz.1, hzt⟩
        · replace hzt := not_le.mp hzt
          have := h z ⟨by linarith, by linarith [hz.2]⟩
          rw [this, haa, hbb]
      have := le_csSup hbdd this
      linarith
    intro y hy
    obtain ⟨t, htS, hty⟩ := exists_lt_of_lt_csSup hne (by rw [hcq]; exact hy.2)
    exact htS.2.2 y ⟨hy.1, le_of_lt hty⟩
  intro y hy
  by_cases hle : y ≤ x₀
  · exact left y ⟨hy.1, hle⟩
  · exact right y ⟨le_of_lt (not_le.mp hle), hy.2⟩

/-- Local affineness on an order-connected set makes `f` affine on all of it.
Reduces to the interval case by widening slightly past the endpoints, where the
endpoints' own affine neighbourhoods still apply. -/
theorem affine_on_ordConnected {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (H : ∀ x ∈ S, ∃ ε > 0, ∃ a b : ℝ, ∀ y ∈ Set.Ioo (x - ε) (x + ε), f y = a * y + b)
    {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ∃ a b : ℝ, ∀ y ∈ S, f y = a * y + b := by
  obtain ⟨e₀, he₀, a₀, b₀, h₀⟩ := H x₀ hx₀
  refine ⟨a₀, b₀, ?_⟩
  intro y hyS
  obtain ⟨ey, hey, ay, cy, hy⟩ := H y hyS
  set d := min ey e₀ with hd
  have hdpos : 0 < d := lt_min hey he₀
  have hdy : d ≤ ey := min_le_left _ _
  have hd0 : d ≤ e₀ := min_le_right _ _
  -- a widened open interval on which `f` is still locally affine everywhere
  have key : ∀ lo hi : ℝ, lo < hi → x₀ ∈ Set.Ioo lo hi → y ∈ Set.Ioo lo hi →
      (∀ x ∈ Set.Ioo lo hi, ∃ ε > 0, ∃ a b : ℝ,
        ∀ z ∈ Set.Ioo (x - ε) (x + ε), f z = a * z + b) → f y = a₀ * y + b₀ := by
    intro lo hi _ hx₀J hyJ hJ
    obtain ⟨a, b, hab⟩ := affine_on_Ioo hJ hx₀J
    -- pin `(a,b)` to `(a₀,b₀)` using two points near `x₀`
    set r := min (min e₀ (x₀ - lo)) (hi - x₀) with hr
    have hrpos : 0 < r := lt_min (lt_min he₀ (by linarith [hx₀J.1])) (by linarith [hx₀J.2])
    have hp1 : x₀ + r/3 ∈ Set.Ioo lo hi :=
      ⟨by linarith [hx₀J.1], by
        have := min_le_right (min e₀ (x₀ - lo)) (hi - x₀); linarith⟩
    have hp2 : x₀ + r/2 ∈ Set.Ioo lo hi :=
      ⟨by linarith [hx₀J.1], by
        have := min_le_right (min e₀ (x₀ - lo)) (hi - x₀); linarith⟩
    have hq1 : x₀ + r/3 ∈ Set.Ioo (x₀ - e₀) (x₀ + e₀) := by
      have := (min_le_left (min e₀ (x₀ - lo)) (hi - x₀)).trans (min_le_left e₀ (x₀ - lo))
      exact ⟨by linarith, by linarith⟩
    have hq2 : x₀ + r/2 ∈ Set.Ioo (x₀ - e₀) (x₀ + e₀) := by
      have := (min_le_left (min e₀ (x₀ - lo)) (hi - x₀)).trans (min_le_left e₀ (x₀ - lo))
      exact ⟨by linarith, by linarith⟩
    obtain ⟨haa, hbb⟩ := affine_unique (by intro h; simp only [add_right_inj] at h; linarith)
      ((hab _ hp1).symm.trans (h₀ _ hq1)) ((hab _ hp2).symm.trans (h₀ _ hq2))
    rw [hab y hyJ, haa, hbb]
  rcases le_total y x₀ with hle | hle
  · refine key (y - d) (x₀ + d) (by linarith) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (fun x hx => ?_)
    rcases lt_or_ge x y with h1 | h1
    · refine ⟨min (x - (y - ey)) (y - x), lt_min (by linarith [hx.1]) (by linarith), ay, cy,
        fun z hz => hy z ⟨?_, ?_⟩⟩
      · have := min_le_left (x - (y - ey)) (y - x); linarith [hz.1]
      · have := min_le_right (x - (y - ey)) (y - x); linarith [hz.2]
    rcases le_or_gt x x₀ with h2 | h2
    · exact H x (hS.out hyS hx₀ ⟨h1, h2⟩)
    · refine ⟨min ((x₀ + e₀) - x) (x - x₀), lt_min (by linarith [hx.2]) (by linarith), a₀, b₀,
        fun z hz => h₀ z ⟨?_, ?_⟩⟩
      · have := min_le_right ((x₀ + e₀) - x) (x - x₀); linarith [hz.1]
      · have := min_le_left ((x₀ + e₀) - x) (x - x₀); linarith [hz.2]
  · refine key (x₀ - d) (y + d) (by linarith) ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩ (fun x hx => ?_)
    rcases lt_or_ge x x₀ with h1 | h1
    · refine ⟨min (x - (x₀ - e₀)) (x₀ - x), lt_min (by linarith [hx.1]) (by linarith), a₀, b₀,
        fun z hz => h₀ z ⟨?_, ?_⟩⟩
      · have := min_le_left (x - (x₀ - e₀)) (x₀ - x); linarith [hz.1]
      · have := min_le_right (x - (x₀ - e₀)) (x₀ - x); linarith [hz.2]
    rcases le_or_gt x y with h2 | h2
    · exact H x (hS.out hx₀ hyS ⟨h1, h2⟩)
    · refine ⟨min ((y + ey) - x) (x - y), lt_min (by linarith [hx.2]) (by linarith), ay, cy,
        fun z hz => hy z ⟨?_, ?_⟩⟩
      · have := min_le_right ((y + ey) - x) (x - y); linarith [hz.1]
      · have := min_le_left ((y + ey) - x) (x - y); linarith [hz.2]

open BrinSquier

/-- On a set where `f` is affine, the moved points split into two order-connected pieces,
divided at the affine map's fixed point (or at `0` when the slope is one). -/
lemma piece_ordConnected {f : ℝ ≃o ℝ} {P : Set ℝ} {a c r : ℝ} (hP : P.OrdConnected)
    (haff : ∀ y ∈ P, f y = a * y + c) (hfix : a ≠ 1 → a * r + c = r) :
    (P ∩ Set.Iio r ∩ supp f).OrdConnected ∧ (P ∩ Set.Ici r ∩ supp f).OrdConnected := by
  -- a point of `P` is moved exactly when it is not the affine fixed point
  have hmoved : ∀ y ∈ P, y ≠ r → a ≠ 1 → y ∈ supp f := by
    intro y hy hyr ha hcon
    have : a * y + c = y := by rw [← haff y hy]; exact hcon
    have hfr := hfix ha
    have : (a - 1) * (y - r) = 0 := by nlinarith [this, hfr]
    rcases mul_eq_zero.1 this with h | h
    · exact ha (by linarith)
    · exact hyr (by linarith)
  constructor
  · constructor
    intro y hy z hz w hw
    refine ⟨⟨hP.out hy.1.1 hz.1.1 hw, lt_of_le_of_lt hw.2 hz.1.2⟩, ?_⟩
    by_cases ha : a = 1
    · -- slope one: moved iff `c ≠ 0`, uniformly on `P`
      have hc : c ≠ 0 := by
        intro hc0
        exact hy.2 (by rw [haff y hy.1.1, ha, hc0]; ring)
      intro hcon
      rw [haff w (hP.out hy.1.1 hz.1.1 hw), ha] at hcon
      exact hc (by linarith)
    · exact hmoved w (hP.out hy.1.1 hz.1.1 hw) (ne_of_lt (lt_of_le_of_lt hw.2 hz.1.2)) ha
  · constructor
    intro y hy z hz w hw
    refine ⟨⟨hP.out hy.1.1 hz.1.1 hw, le_trans hy.1.2 hw.1⟩, ?_⟩
    by_cases ha : a = 1
    · have hc : c ≠ 0 := by
        intro hc0
        exact hy.2 (by rw [haff y hy.1.1, ha, hc0]; ring)
      intro hcon
      rw [haff w (hP.out hy.1.1 hz.1.1 hw), ha] at hcon
      exact hc (by linarith)
    · -- `y` is moved and `≥ r`, hence `> r`, so `w > r` too
      have hyr : y ≠ r := by
        intro h
        apply hy.2
        rw [haff y hy.1.1, h, hfix ha]
      have : r < w := lt_of_lt_of_le (lt_of_le_of_ne hy.1.2 (Ne.symm hyr)) hw.1
      exact hmoved w (hP.out hy.1.1 hz.1.1 hw) (Ne.symm (ne_of_lt this)) ha

/-- If an open set is covered by finitely many connected subsets, it has finitely many
connected components. -/
theorem finite_components_of_finite_cover {α : Type*} [TopologicalSpace α] {U : Set α}
    {ι : Type*} [Finite ι] (V : ι → Set α)
    (hconn : ∀ i, IsPreconnected (V i)) (hsub : ∀ i, V i ⊆ U) (hcov : U ⊆ ⋃ i, V i) :
    {C : Set α | ∃ x ∈ U, C = connectedComponentIn U x}.Finite :=
  TopCover.finite_components_of_finite_cover V hconn hsub hcov


end BS_all

open BS_all BrinSquier in
theorem solution {f : ℝ ≃o ℝ} (hf : IsPLF f) :
    {C : Set ℝ | ∃ x ∈ supp f, C = connectedComponentIn (supp f) x}.Finite := by
  classical
  obtain ⟨B, hB⟩ := hf
  -- `f` is affine on each breakpoint gap
  have hdb : ∀ b : ℝ, ∃ ac : ℝ × ℝ, ∀ y ∈ gapBelow B b, f y = ac.1 * y + ac.2 := by
    intro b
    by_cases hne : (gapBelow B b).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      obtain ⟨a, c, hac⟩ := affine_on_ordConnected (gapBelow_ordConnected B b)
        (fun x hx => hB x (gapBelow_disj B b x hx)) hx₀
      exact ⟨(a, c), hac⟩
    · exact ⟨(0, 0), fun y hy => absurd ⟨y, hy⟩ hne⟩
  choose datB hdatB using hdb
  have hdt : ∃ ac : ℝ × ℝ, ∀ y ∈ gapTop B, f y = ac.1 * y + ac.2 := by
    by_cases hne : (gapTop B).Nonempty
    · obtain ⟨x₀, hx₀⟩ := hne
      obtain ⟨a, c, hac⟩ := affine_on_ordConnected (gapTop_ordConnected B)
        (fun x hx => hB x (gapTop_disj B x hx)) hx₀
      exact ⟨(a, c), hac⟩
    · exact ⟨(0, 0), fun y hy => absurd ⟨y, hy⟩ hne⟩
  obtain ⟨datT, hdatT⟩ := hdt
  -- the split point on each gap: the affine fixed point, or `0` when the slope is one
  set rB : ℝ → ℝ := fun b => if (datB b).1 = 1 then 0 else (datB b).2 / (1 - (datB b).1) with hrB
  set rT : ℝ := if datT.1 = 1 then 0 else datT.2 / (1 - datT.1) with hrT
  have hfixB : ∀ b, (datB b).1 ≠ 1 → (datB b).1 * rB b + (datB b).2 = rB b := by
    intro b ha
    have h1 : (1 : ℝ) - (datB b).1 ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
    simp only [hrB, if_neg ha]
    field_simp
    ring
  have hfixT : datT.1 ≠ 1 → datT.1 * rT + datT.2 = rT := by
    intro ha
    have h1 : (1 : ℝ) - datT.1 ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
    simp only [hrT, if_neg ha]
    field_simp
    ring
  -- the finite cover
  refine finite_components_of_finite_cover
    (ι := ((↑B ⊕ Unit) × Bool) ⊕ (↑B : Type))
    (fun idx => match idx with
      | Sum.inl (Sum.inl b, false) => gapBelow B (b : ℝ) ∩ Set.Iio (rB (b : ℝ)) ∩ supp f
      | Sum.inl (Sum.inl b, true) => gapBelow B (b : ℝ) ∩ Set.Ici (rB (b : ℝ)) ∩ supp f
      | Sum.inl (Sum.inr _, false) => gapTop B ∩ Set.Iio rT ∩ supp f
      | Sum.inl (Sum.inr _, true) => gapTop B ∩ Set.Ici rT ∩ supp f
      | Sum.inr b => {(b : ℝ)} ∩ supp f) ?_ ?_ ?_
  · rintro (⟨(b | _), (_ | _)⟩ | b)
    · exact ((piece_ordConnected (gapBelow_ordConnected B _) (hdatB _)
        (hfixB _)).1).isPreconnected
    · exact ((piece_ordConnected (gapBelow_ordConnected B _) (hdatB _)
        (hfixB _)).2).isPreconnected
    · exact ((piece_ordConnected (gapTop_ordConnected B) hdatT hfixT).1).isPreconnected
    · exact ((piece_ordConnected (gapTop_ordConnected B) hdatT hfixT).2).isPreconnected
    · exact (Set.subsingleton_singleton.anti Set.inter_subset_left).isPreconnected
  · rintro (⟨(b | _), (_ | _)⟩ | b) <;> intro y hy
    · exact hy.2
    · exact hy.2
    · exact hy.2
    · exact hy.2
    · exact hy.2
  · intro y hy
    rcases gaps_cover B y with hb | ht | ⟨b, hbB, hgb⟩
    · exact Set.mem_iUnion.2 ⟨Sum.inr ⟨y, Finset.mem_coe.mp hb⟩, ⟨rfl, hy⟩⟩
    · rcases lt_or_ge y rT with h | h
      · exact Set.mem_iUnion.2 ⟨Sum.inl (Sum.inr (), false), ⟨⟨ht, h⟩, hy⟩⟩
      · exact Set.mem_iUnion.2 ⟨Sum.inl (Sum.inr (), true), ⟨⟨ht, h⟩, hy⟩⟩
    · rcases lt_or_ge y (rB b) with h | h
      · exact Set.mem_iUnion.2 ⟨Sum.inl (Sum.inl ⟨b, hbB⟩, false), ⟨⟨hgb, h⟩, hy⟩⟩
      · exact Set.mem_iUnion.2 ⟨Sum.inl (Sum.inl ⟨b, hbB⟩, true), ⟨⟨hgb, h⟩, hy⟩⟩
