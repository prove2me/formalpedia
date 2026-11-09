-- Prove2me | solution 1 for CorrelatedLocalSearch.eq_21_one_step
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:50:46.303148+00:00
-- url     : https://prove2.me/submissions/b6dffa19-23d6-478f-ac2e-8132213300d2

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess

set_option autoImplicit false

open Classical

open CorrelatedLocalSearch in
theorem solution (k r : ℕ) (hk : k < 2 * r) (hr : r < k)
    (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ)
    (hP : IsPotentialProcess k r live pot h) (w : List (Fin k)) (hw : Surv live w)
    (f : ℕ → ℝ) (hf0 : f 0 = 0) (hfnn : ∀ d, 0 ≤ f d) (hfmono : Monotone f) :
    (k : ℝ) ^ (-sStar k r) * ∑ a : Fin k, (if live (w ++ [a]) then f (pot (w ++ [a])) else 0) ≤
      (r : ℝ) * (k : ℝ) ^ (-sStar k r) * f (pot w - 1) +
        ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) * f (pot w + 1) := by
  set c := (k : ℝ) ^ (-sStar k r) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg k) _
  set g : Fin k → ℝ := fun a => if live (w ++ [a]) then f (pot (w ++ [a])) else 0 with hg
  set T : Finset (Fin k) := Finset.univ.filter
    (fun a => ¬ live (w ++ [a]) ∨ pot (w ++ [a]) + 1 ≤ pot w) with hT
  have hTcard : r ≤ T.card := by
    have h1 := hP.down w hw
    have e : {a : Fin k | ¬ live (w ++ [a]) ∨ pot (w ++ [a]) + 1 ≤ pot w} = (T : Set (Fin k)) := by
      ext a; simp [hT]
    rw [e, Set.ncard_coe_finset] at h1
    exact h1
  have hcard : T.card + (Finset.univ.filter
      (fun a => ¬ (¬ live (w ++ [a]) ∨ pot (w ++ [a]) + 1 ≤ pot w))).card = k := by
    rw [hT, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hle1 : ∀ a ∈ T, g a ≤ f (pot w - 1) := by
    intro a ha
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [hg]
    by_cases hl : live (w ++ [a])
    · rw [if_pos hl]
      have : pot (w ++ [a]) + 1 ≤ pot w := ha.resolve_left (not_not.mpr hl)
      exact hfmono (by omega)
    · rw [if_neg hl]; exact hfnn _
  have hle2 : ∀ a, g a ≤ f (pot w + 1) := by
    intro a
    simp only [hg]
    by_cases hl : live (w ++ [a])
    · rw [if_pos hl]
      have : pot (w ++ [a]) ≤ pot w + 1 := (hP.up w hw a).resolve_left (not_not.mpr hl)
      exact hfmono this
    · rw [if_neg hl]; exact hfnn _
  set Tc : Finset (Fin k) := Finset.univ.filter
    (fun a => ¬ (¬ live (w ++ [a]) ∨ pot (w ++ [a]) + 1 ≤ pot w)) with hTc
  have hsplit : ∑ a ∈ T, g a + ∑ a ∈ Tc, g a = ∑ a, g a := by
    rw [hT, hTc]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ _ g
  have b1 : ∑ a ∈ T, g a ≤ (T.card : ℝ) * f (pot w - 1) := by
    have := Finset.sum_le_card_nsmul T g (f (pot w - 1)) hle1
    rwa [nsmul_eq_mul] at this
  have b2 : ∑ a ∈ Tc, g a ≤ (Tc.card : ℝ) * f (pot w + 1) := by
    have := Finset.sum_le_card_nsmul Tc g (f (pot w + 1)) (fun a _ => hle2 a)
    rwa [nsmul_eq_mul] at this
  have hcardR : (T.card : ℝ) + (Tc.card : ℝ) = k := by
    exact_mod_cast hcard
  have hTr : (r : ℝ) ≤ T.card := by exact_mod_cast hTcard
  have hf12 : f (pot w - 1) ≤ f (pot w + 1) := hfmono (by omega)
  have hsum : ∑ a, g a ≤ (r : ℝ) * f (pot w - 1) + ((k : ℝ) - r) * f (pot w + 1) := by
    rw [← hsplit]
    have e1 := congrArg (fun z => z * f (pot w + 1)) hcardR
    nlinarith [mul_nonneg (sub_nonneg.mpr hTr) (sub_nonneg.mpr hf12)]
  have := mul_le_mul_of_nonneg_left hsum hc0
  linarith
