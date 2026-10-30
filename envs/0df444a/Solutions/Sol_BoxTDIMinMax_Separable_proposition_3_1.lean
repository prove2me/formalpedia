-- Prove2me | solution 1 for BoxTDIMinMax.Separable.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:03:22.294595+00:00
-- url     : https://prove2.me/submissions/7b989837-1087-49a6-bca5-db2a99492848

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable.Prop31Aux

open BoxTDIMinMax.Separable

theorem top_or (x : WithTop ℤ) : x = ⊤ ∨ ∃ a : ℤ, (a : WithTop ℤ) = x := by
  by_cases h : x = ⊤
  · exact Or.inl h
  · exact Or.inr (WithTop.ne_top_iff_exists.mp h)

/-- One-sided form: slopes to the right of a fitting point stay `≥ l`, and hence
`φ(k + n) ≥ φ(k) + n l` for all `n ≥ 0`. -/
theorem right_side (φ : ℤ → WithTop ℤ) (hφ : DiscConvex φ) (k l : ℤ)
    (hfit : Fitting φ k l) :
    ∀ n : ℕ, φ (k + n) + (l : WithTop ℤ) ≤ φ (k + n + 1) ∧
      φ k + (((n : ℤ) * l : ℤ) : WithTop ℤ) ≤ φ (k + n) := by
  obtain ⟨hk, _, hr⟩ := hfit
  obtain ⟨hconv, hint⟩ := hφ
  intro n
  induction n with
  | zero => simpa using hr
  | succ n ih =>
    obtain ⟨hA, hB⟩ := ih
    have hcast : ((k + ((n + 1 : ℕ) : ℤ)) : ℤ) = k + n + 1 := by push_cast; ring
    rw [hcast]
    constructor
    · -- slope at `m = k + n + 1`
      by_cases hm : φ (k + n + 1) = ⊤
      · have h2 : φ (k + n + 1 + 1) = ⊤ := by
          by_contra h2
          exact (hint k (k + n + 1) (k + n + 1 + 1) (by omega) (by omega) hk h2) hm
        rw [h2]; exact le_top
      · have hm1 : φ (k + n) ≠ ⊤ :=
          hint k (k + n) (k + n + 1) (by omega) (by omega) hk hm
        have hc := hconv (k + n + 1) hm
        have e1 : k + n + 1 - 1 = k + n := by ring
        rw [e1] at hc
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hm
        obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hm1
        rw [← ha, ← hb] at hc
        rw [← ha, ← hb] at hA
        rw [← ha]
        rcases BoxTDIMinMax.Separable.Prop31Aux.top_or (φ (k + n + 1 + 1)) with h3 | ⟨c, hc3⟩
        · rw [h3]; exact le_top
        · rw [← hc3] at hc ⊢
          have hA' : b + l ≤ a := by exact_mod_cast hA
          have hc' : a + a ≤ b + c := by exact_mod_cast hc
          exact_mod_cast (show a + l ≤ c by omega)
    · by_cases hm : φ (k + n + 1) = ⊤
      · rw [hm]; exact le_top
      · have hm1 : φ (k + n) ≠ ⊤ :=
          hint k (k + n) (k + n + 1) (by omega) (by omega) hk hm
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hm
        obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hm1
        obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hk
        rw [← ha, ← hb] at hA
        rw [← hb, ← hc] at hB
        rw [← ha, ← hc]
        have hA' : b + l ≤ a := by exact_mod_cast hA
        have hB' : c + (n : ℤ) * l ≤ b := by exact_mod_cast hB
        have : c + ((n + 1 : ℕ) : ℤ) * l ≤ a := by push_cast; nlinarith
        exact_mod_cast this

theorem reflect_convex (φ : ℤ → WithTop ℤ) (hφ : DiscConvex φ) :
    DiscConvex (fun k => φ (-k)) := by
  obtain ⟨hconv, hint⟩ := hφ
  refine ⟨fun k hk => ?_, fun a b c hab hbc ha hc => ?_⟩
  · have := hconv (-k) hk
    simp only at hk ⊢
    have e1 : -(k - 1) = -k + 1 := by ring
    have e2 : -(k + 1) = -k - 1 := by ring
    rw [e1, e2, add_comm (φ (-k + 1))]
    exact this
  · simp only at ha hc ⊢
    exact hint (-c) (-b) (-a) (by omega) (by omega) hc ha

theorem le_of_ge (φ : ℤ → WithTop ℤ) (hφ : DiscConvex φ) (kStar lStar : ℤ)
    (hfit : Fitting φ kStar lStar) (k : ℤ) (hk : kStar ≤ k) :
    φ kStar + ((lStar * k : ℤ) : WithTop ℤ) ≤ φ k + ((lStar * kStar : ℤ) : WithTop ℤ) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = kStar + n := ⟨(k - kStar).toNat, by omega⟩
  have h := (right_side φ hφ kStar lStar hfit n).2
  rw [← hn] at h
  rcases BoxTDIMinMax.Separable.Prop31Aux.top_or (φ k) with h3 | ⟨c, hc3⟩
  · rw [h3]; simp
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hfit.1
    rw [← hc3, ← ha] at h ⊢
    have h' : a + (n : ℤ) * lStar ≤ c := by exact_mod_cast h
    have : a + lStar * k ≤ c + lStar * kStar := by rw [hn]; nlinarith
    exact_mod_cast this

end BoxTDIMinMax.Separable.Prop31Aux

open BoxTDIMinMax.Separable in
theorem solution (φ : ℤ → WithTop ℤ) (hφ : DiscConvex φ) (kStar lStar : ℤ)
    (hfit : Fitting φ kStar lStar) (k : ℤ) :
    φ kStar + ((lStar * k : ℤ) : WithTop ℤ) ≤ φ k + ((lStar * kStar : ℤ) : WithTop ℤ) := by
  rcases le_total kStar k with hk | hk
  · exact BoxTDIMinMax.Separable.Prop31Aux.le_of_ge φ hφ kStar lStar hfit k hk
  · -- reflect
    have hψ := BoxTDIMinMax.Separable.Prop31Aux.reflect_convex φ hφ
    have hfit' : Fitting (fun k => φ (-k)) (-kStar) (-lStar) := by
      obtain ⟨h0, h1, h2⟩ := hfit
      refine ⟨by simpa using h0, ?_, ?_⟩
      · simp only [neg_neg]
        have e : -(-kStar - 1) = kStar + 1 := by ring
        rw [e]
        rcases BoxTDIMinMax.Separable.Prop31Aux.top_or (φ (kStar + 1)) with h3 | ⟨c, hc3⟩
        · rw [h3]; simp
        · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h0
          rw [← hc3, ← ha] at h2 ⊢
          have : a + lStar ≤ c := by exact_mod_cast h2
          exact_mod_cast (show a ≤ c + -lStar by omega)
      · simp only [neg_neg]
        have e : -(-kStar + 1) = kStar - 1 := by ring
        rw [e]
        rcases BoxTDIMinMax.Separable.Prop31Aux.top_or (φ (kStar - 1)) with h3 | ⟨c, hc3⟩
        · rw [h3]; simp
        · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp h0
          rw [← hc3, ← ha] at h1 ⊢
          have : a ≤ c + lStar := by exact_mod_cast h1
          exact_mod_cast (show a + -lStar ≤ c by omega)
    have h := BoxTDIMinMax.Separable.Prop31Aux.le_of_ge _ hψ (-kStar) (-lStar) hfit' (-k)
      (by omega)
    simp only [neg_neg, neg_mul_neg] at h
    exact h
