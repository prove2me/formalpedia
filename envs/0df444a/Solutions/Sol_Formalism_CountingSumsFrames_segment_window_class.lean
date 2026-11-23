-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_window_class
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:40.657582+00:00
-- url     : https://prove2.me/submissions/a591506c-9c93-4b30-b77c-6321b18098d8

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegWindowClass := by
  intro a n P sg hP hsg
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsg
  obtain ⟨c, hc⟩ : ∃ c, c = (d + P - 1) / P := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = (d + n + P - 1) / P := ⟨_, rfl⟩
  have hce : c ≤ e := by rw [hc, he]; exact Nat.div_le_div_right (by omega)
  have key : ∀ m, c ≤ m ↔ d ≤ P * m := by
    intro m
    rw [hc, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hP]
    have : (m+1) * P = P * m + P := by ring
    rw [Nat.succ_eq_add_one, this]; omega
  have key2 : ∀ m, m < e ↔ P * m < d + n := by
    intro m
    rw [he, ← Nat.succ_le_iff, Nat.le_div_iff_mul_le hP]
    have : (m+1) * P = P * m + P := by ring
    rw [Nat.succ_eq_add_one, this]; omega
  have hdiv : ∀ x, sg + d ≤ x → x % P = sg % P → P * ((x - sg) / P) = x - sg := by
    intro x hx hm
    have : P ∣ x - sg := (Nat.modEq_iff_dvd' (by omega)).1 (show sg ≡ x [MOD P] from hm.symm)
    exact Nat.mul_div_cancel' this
  have himg : ((Ico (sg + d) (sg + d + n)).filter (fun x => x % P = sg % P)).image (fun x => (x - sg) / P)
      = Ico c (c + (e - c)) := by
    ext m
    simp only [mem_image, mem_filter, mem_Ico]
    constructor
    · rintro ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, rfl⟩
      have h := hdiv x hx1 hx3
      refine ⟨(key _).2 (by omega), ?_⟩
      have : (x - sg) / P < e := (key2 _).2 (by omega)
      omega
    · rintro ⟨h1, h2⟩
      have h1' := (key m).1 h1
      have h2' := (key2 m).1 (by omega)
      refine ⟨sg + P * m, ⟨⟨by omega, by omega⟩, Nat.add_mul_mod_self_left _ _ _⟩, ?_⟩
      rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left m hP]
  refine ⟨c, e - c, himg, ?_, ?_, ?_⟩
  · rw [← Finset.card_image_of_injOn (f := fun x => (x - sg) / P), himg]
    · simp
    · intro x hx y hy hxy
      have hx' := mem_filter.1 hx
      have hy' := mem_filter.1 hy
      have hx1 := (mem_Ico.1 hx'.1).1
      have hy1 := (mem_Ico.1 hy'.1).1
      have ex := hdiv x hx1 hx'.2
      have ey := hdiv y hy1 hy'.2
      simp only at hxy
      rw [hxy] at ex
      omega
  · have h1 : d + n + P - 1 = (d + P - 1) + n := by omega
    rw [he, hc, h1, Nat.add_div hP]
    generalize (d + P - 1) / P = u
    generalize n / P = v
    split_ifs <;> omega
  · have h1 : d + n + P - 1 = (d + P - 1) + n := by omega
    rw [he, hc, h1, Nat.add_div hP]
    generalize (d + P - 1) / P = u
    generalize n / P = v
    split_ifs <;> omega
end Formalism.CountingSumsFrames
