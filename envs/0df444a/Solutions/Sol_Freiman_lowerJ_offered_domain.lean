-- Prove2me | solution 1 for Freiman.lowerJ_offered_domain
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:51:55.461105+00:00
-- url     : https://prove2.me/submissions/f27fdb28-3e02-4810-9c2d-51ba707ebbdc

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

namespace M7J

theorem cd_eq (w : List ℕ+) : lowerCD w =
    List.foldl (fun z (a : ℕ) => (z.2, z.1 + a * z.2)) (0, 1) (w.map PNat.val) := by
  have hbind : (do let a ← w; pure (a : ℕ)) = w.map PNat.val := by
    induction w with
    | nil => rfl
    | cons a w ih => simpa using ih
  unfold lowerCD
  rw [hbind]

theorem cd_append (w : List ℕ+) (a : ℕ+) :
    lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a : ℕ) * (lowerCD w).2) := by
  rw [cd_eq, cd_eq, List.map_append, List.foldl_append]
  simp

theorem cd_pos : ∀ w : List ℕ+, 0 < (lowerCD w).2 := by
  intro w
  induction w using List.reverseRecOn with
  | nil => rw [cd_eq]; norm_num
  | append_singleton w a ih =>
      rw [cd_append]
      show 0 < (lowerCD w).1 + (a : ℕ) * (lowerCD w).2
      have h1 : 0 < (a : ℕ) * (lowerCD w).2 := Nat.mul_pos a.pos ih
      omega

lemma alpha_pos : 0 < lowerAlpha := by
  unfold lowerAlpha
  have : (3:ℝ) < Real.sqrt 21 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

lemma beta_gt_alpha : lowerAlpha < lowerBeta := by
  unfold lowerAlpha lowerBeta
  have : (3:ℝ) < Real.sqrt 21 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- the run-offer width inequality in terms of the continuants -/
lemma key (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2)))
    (u v : List ℕ+) (h : (7/5 : ℝ)*lowerWidth (v ++ [3]) < lowerWidth (u ++ [3])) :
    (7/5 : ℝ) * ((((lowerCD u).2:ℝ)*lowerAlpha + ((lowerCD u).1 + 3*(lowerCD u).2))*
        (((lowerCD u).2:ℝ)*lowerBeta + ((lowerCD u).1 + 3*(lowerCD u).2))) <
      ((((lowerCD v).2:ℝ)*lowerAlpha + ((lowerCD v).1 + 3*(lowerCD v).2))*
        (((lowerCD v).2:ℝ)*lowerBeta + ((lowerCD v).1 + 3*(lowerCD v).2))) := by
  rw [hw, hw, cd_append, cd_append] at h
  simp only [Nat.cast_add, Nat.cast_mul, PNat.val_ofNat, Nat.cast_ofNat] at h
  have ha := alpha_pos
  have hab := beta_gt_alpha
  have hb : 0 < lowerBeta := by linarith
  have du : (0:ℝ) < (lowerCD u).2 := by exact_mod_cast cd_pos u
  have dv : (0:ℝ) < (lowerCD v).2 := by exact_mod_cast cd_pos v
  have cu : (0:ℝ) ≤ (lowerCD u).1 := by positivity
  have cv : (0:ℝ) ≤ (lowerCD v).1 := by positivity
  set Nu := ((((lowerCD u).2:ℝ)*lowerAlpha + ((lowerCD u).1 + 3*(lowerCD u).2))*
        (((lowerCD u).2:ℝ)*lowerBeta + ((lowerCD u).1 + 3*(lowerCD u).2))) with hNu
  set Nv := ((((lowerCD v).2:ℝ)*lowerAlpha + ((lowerCD v).1 + 3*(lowerCD v).2))*
        (((lowerCD v).2:ℝ)*lowerBeta + ((lowerCD v).1 + 3*(lowerCD v).2))) with hNv
  have hNu0 : 0 < Nu := by rw [hNu]; positivity
  have hNv0 : 0 < Nv := by rw [hNv]; positivity
  have h' : (7/5 : ℝ) * ((lowerBeta - lowerAlpha) / Nv) < (lowerBeta - lowerAlpha) / Nu := h
  rw [← mul_div_assoc, div_lt_div_iff₀ hNv0 hNu0] at h'
  have hba : 0 < lowerBeta - lowerAlpha := by linarith
  nlinarith

end M7J

open M7J

theorem solution (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) : lowerJDomain (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) (lowerScale (lowerNormalize p)) := by
  obtain ⟨-, -, -, hbox⟩ := hs
  obtain ⟨-, h3, -, -, hrun⟩ := hr
  -- the parameter box for the normalized pair
  have hbox' : (1/4 : ℝ) ≤ lowerRatio (lowerNormalize p).1 ∧ lowerRatio (lowerNormalize p).1 ≤ 4/5 ∧
      (1/4 : ℝ) ≤ lowerRatio (lowerNormalize p).2 ∧ lowerRatio (lowerNormalize p).2 ≤ 4/5 := by
    unfold lowerNormalize
    split_ifs
    · exact hbox
    · exact ⟨hbox.2.2.1, hbox.2.2.2, hbox.1, hbox.2.1⟩
  refine ⟨⟨hbox'.1, hbox'.2.1⟩, ⟨hbox'.2.2.1, hbox'.2.2.2⟩, ?_, ?_⟩
  · -- H7 ≤ q from ¬ A3
    have h3' : ¬ (lowerScale (lowerNormalize p) < lowerThreshold p (31/100) 3 63 25 66) := h3
    rw [not_lt] at h3'
    have e : lowerJH7 (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) =
        lowerThreshold p (31/100) 3 63 25 66 := by
      unfold lowerJH7 lowerJH lowerJA lowerJA2 lowerJE lowerJX lowerThreshold
      ring
    rw [e]; exact h3'
  · -- q < HStar from the run offer
    have hk := key hw (lowerNormalize p).1 (lowerNormalize p).2 hrun
    have ha := alpha_pos
    have hab := beta_gt_alpha
    have hb : 0 < lowerBeta := by linarith
    set c1 : ℝ := ((lowerCD (lowerNormalize p).1).1 : ℝ) with hc1
    set d1 : ℝ := ((lowerCD (lowerNormalize p).1).2 : ℝ) with hd1
    set c2 : ℝ := ((lowerCD (lowerNormalize p).2).1 : ℝ) with hc2
    set d2 : ℝ := ((lowerCD (lowerNormalize p).2).2 : ℝ) with hd2
    have d1p : 0 < d1 := by rw [hd1]; exact_mod_cast cd_pos _
    have d2p : 0 < d2 := by rw [hd2]; exact_mod_cast cd_pos _
    have c1n : 0 ≤ c1 := by rw [hc1]; positivity
    have c2n : 0 ≤ c2 := by rw [hc2]; positivity
    unfold lowerJHStar lowerJH lowerScale lowerRatio
    simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat]
    rw [← hc1, ← hd1, ← hc2, ← hd2]
    have h3a : 0 < 3 + lowerAlpha := by linarith
    have h3b : 0 < 3 + lowerBeta := by linarith
    have e1 : 1 + c1/d1 * (1/(3+lowerAlpha)) = (d1*lowerAlpha + (c1 + 3*d1)) / (d1*(3+lowerAlpha)) := by
      field_simp; ring
    have e2 : 1 + c1/d1 * (1/(3+lowerBeta)) = (d1*lowerBeta + (c1 + 3*d1)) / (d1*(3+lowerBeta)) := by
      field_simp; ring
    have e3 : 1 + c2/d2 * (1/(3+lowerAlpha)) = (d2*lowerAlpha + (c2 + 3*d2)) / (d2*(3+lowerAlpha)) := by
      field_simp; ring
    have e4 : 1 + c2/d2 * (1/(3+lowerBeta)) = (d2*lowerBeta + (c2 + 3*d2)) / (d2*(3+lowerBeta)) := by
      field_simp; ring
    rw [e1, e2, e3, e4]
    set Nu := (d1*lowerAlpha + (c1 + 3*d1)) * (d1*lowerBeta + (c1 + 3*d1)) with hNu
    set Nv := (d2*lowerAlpha + (c2 + 3*d2)) * (d2*lowerBeta + (c2 + 3*d2)) with hNv
    have hNu0 : 0 < Nu := by rw [hNu]; positivity
    have hNv0 : 0 < Nv := by rw [hNv]; positivity
    have eq : (5/7 : ℝ) * ((d2*lowerAlpha + (c2 + 3*d2)) / (d2*(3+lowerAlpha))) * ((d2*lowerBeta + (c2 + 3*d2)) / (d2*(3+lowerBeta))) /
        (((d1*lowerAlpha + (c1 + 3*d1)) / (d1*(3+lowerAlpha))) * ((d1*lowerBeta + (c1 + 3*d1)) / (d1*(3+lowerBeta)))) =
        d1^2/d2^2 * ((5/7) * Nv / Nu) := by
      rw [hNu, hNv]
      field_simp
    rw [eq]
    have hq : 0 < d1^2/d2^2 := by positivity
    have : 1 < (5/7) * Nv / Nu := by
      rw [lt_div_iff₀ hNu0]; linarith
    calc d1^2/d2^2 = d1^2/d2^2 * 1 := by ring
      _ < d1^2/d2^2 * ((5/7) * Nv / Nu) := by exact mul_lt_mul_of_pos_left this hq
