-- Prove2me | solution 1 for Freiman.lowerJ_equal_contact
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T17:33:38.476651+00:00
-- url     : https://prove2.me/submissions/c6294543-8a5a-4d5e-b655-ccd666aad045

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

open Freiman

namespace M7JEC

lemma pe_nonneg (w : List ℕ+) : ∀ (x : ℝ), 0 ≤ x → 0 ≤ prefixEval w x := by
  induction w with
  | nil => intro x hx; simpa [prefixEval] using hx
  | cons a w ih =>
      intro x hx
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have h := ih x hx
      have hd : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      simp only [prefixEval]
      positivity

lemma pe_append (u : List ℕ+) : ∀ (v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => intro v x; simp [prefixEval]
  | cons a u ih => intro v x; simp only [List.cons_append, prefixEval, ih]

lemma cd_append (u v : List ℕ+) :
    lowerCD (u ++ v) = v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (lowerCD u) := by
  simp [lowerCD, List.foldl_append]

lemma cd_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact Nat.one_pos
  | append_singleton w a ih =>
      rw [cd_append]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos a.property ih) (Nat.le_add_left _ _)

lemma den_pos (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    (0:ℝ) < ((lowerCD w).1 : ℝ) * x + ((lowerCD w).2 : ℝ) := by
  have h1 : (0:ℝ) ≤ ((lowerCD w).1 : ℝ) := Nat.cast_nonneg _
  have h2 : (0:ℝ) < ((lowerCD w).2 : ℝ) := by exact_mod_cast cd_pos w
  nlinarith

lemma pe_rep (w : List ℕ+) : ∃ a b : ℕ,
    (∀ x : ℝ, 0 ≤ x → prefixEval w x
      = ((a:ℝ)*x + (b:ℝ))/(((lowerCD w).1 : ℝ)*x + ((lowerCD w).2 : ℝ))) ∧
    (a:ℝ)*((lowerCD w).2 : ℝ) - (b:ℝ)*((lowerCD w).1 : ℝ) = (-1:ℝ)^w.length := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨1, 0, ?_, ?_⟩
      · intro x hx; simp [prefixEval, lowerCD]
      · simp [lowerCD]
  | append_singleton w d ih =>
      obtain ⟨a, b, hev, hdet⟩ := ih
      have hcd : lowerCD (w ++ [d]) = ((lowerCD w).2, (lowerCD w).1 + (d:ℕ) * (lowerCD w).2) := by
        rw [cd_append]; rfl
      refine ⟨b, a + (d:ℕ)*b, ?_, ?_⟩
      · intro x hx
        have hdx : (0:ℝ) < ((d:ℕ):ℝ) + x := by
          have : (1:ℝ) ≤ ((d:ℕ):ℝ) := by exact_mod_cast d.property
          linarith
        have hy : (0:ℝ) ≤ 1/(((d:ℕ):ℝ) + x) := by positivity
        have hstep : prefixEval (w ++ [d]) x = prefixEval w (1/(((d:ℕ):ℝ) + x)) := by
          rw [pe_append]; rfl
        rw [hstep, hev _ hy, hcd]
        have hden := den_pos w (1/(((d:ℕ):ℝ) + x)) hy
        have hden2 := den_pos (w ++ [d]) x hx
        rw [hcd] at hden2
        push_cast at hden2 ⊢
        rw [div_eq_div_iff (by linarith) (by linarith)]
        field_simp
        ring
      · rw [hcd]
        push_cast
        simp only [List.length_append, List.length_cons, List.length_nil, pow_add, pow_one]
        linear_combination -hdet

lemma pe_diff (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    prefixEval w x - prefixEval w y
      = (-1:ℝ)^w.length * (x - y)
        / ((((lowerCD w).1 : ℝ)*x + ((lowerCD w).2 : ℝ)) * (((lowerCD w).1 : ℝ)*y + ((lowerCD w).2 : ℝ))) := by
  obtain ⟨a, b, hev, hdet⟩ := pe_rep w
  rw [hev x hx, hev y hy, div_sub_div _ _ (ne_of_gt (den_pos w x hx)) (ne_of_gt (den_pos w y hy))]
  congr 1
  linear_combination (x - y) * hdet

lemma sign_eq (m n : ℕ) (h : m % 2 = n % 2) : ((-1:ℝ))^m = ((-1:ℝ))^n := by
  rcases Nat.even_or_odd m with hm | hm
  · have hn : Even n := by rw [Nat.even_iff] at hm ⊢; omega
    rw [hm.neg_one_pow, hn.neg_one_pow]
  · have hn : Odd n := by rw [Nat.odd_iff] at hm ⊢; omega
    rw [hm.neg_one_pow, hn.neg_one_pow]


lemma pe_nil (x : ℝ) : prefixEval [] x = x := rfl

lemma alg_e1 (c d α : ℝ) (hrel : 3*α^2+3*α = 1) :
    (d + c*α) * (d*(3+α) + c) = α * ((d*α + (c+3*d))*(d*(3*α) + (c+3*d))) := by
  linear_combination (-(d*(d*α+c+3*d))) * hrel

lemma alg_e2 (a b α : ℝ) (hrel : 3*α^2+3*α = 1) :
    (b*(1+3*α)+a)*(4+3*α)*(b*(7+2*α)+a*(4+α))
      = ((a+2*b)*α + (4*a+7*b))*((a+2*b)*(3*α) + (4*a+7*b)) := by
  linear_combination (3*b*((a+2*b)*α + (4*a+7*b))) * hrel

lemma clause2_core (a b c d α β : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hA0 : 0 < α) (hna : 0 ≤ a) (hnc : 0 ≤ c)
    (hab : β = 3*α) (hrel : 3*α^2+3*α = 1)
    (hV : 0 < (1 + a/b*(1/(1+β)))*(1 + a/b*((4+α)/(7+2*α))))
    (hq : (269/1000:ℝ)*((1 + c/d*α)*(1 + c/d*(1/(3+α))))
            /((1 + a/b*(1/(1+β)))*(1 + a/b*((4+α)/(7+2*α)))) < b^2/d^2)
    (hc2 : (7/5:ℝ)*(3+α) < (269/1000)*(α*((7+2*α)*(4+β)*(1+β)))) :
    (7/5:ℝ)*((d*α + (c+3*d))*(d*β + (c+3*d)))
      < ((a+2*b)*α + (4*a+7*b))*((a+2*b)*β + (4*a+7*b)) := by
  subst hab
  have h3a : (0:ℝ) < 3+α := by linarith
  have h7a : (0:ℝ) < 7+2*α := by linarith
  have h1b : (0:ℝ) < 1+3*α := by linarith
  have h4b : (0:ℝ) < 4+3*α := by linarith
  have hM : (0:ℝ) < (7+2*α)*(4+3*α)*(1+3*α) := mul_pos (mul_pos h7a h4b) h1b
  have hPa : (0:ℝ) < d*α + (c+3*d) := by linarith [mul_pos hd hA0]
  have hPb : (0:ℝ) < d*(3*α) + (c+3*d) := by linarith [mul_pos hd hA0]
  have hQa : (0:ℝ) < (a+2*b)*α + (4*a+7*b) := by
    linarith [mul_nonneg hna hA0.le, mul_pos hb hA0]
  have hQb : (0:ℝ) < (a+2*b)*(3*α) + (4*a+7*b) := by
    linarith [mul_nonneg hna hA0.le, mul_pos hb hA0]
  have hd2 : (0:ℝ) < d^2 := by positivity
  have e1 : d^2 * ((1 + c/d*α)*(1 + c/d*(1/(3+α)))) * (3+α)
      = α * ((d*α + (c+3*d))*(d*(3*α) + (c+3*d))) := by
    have hstep : d^2 * ((1 + c/d*α)*(1 + c/d*(1/(3+α)))) * (3+α)
        = (d + c*α)*(d*(3+α) + c) := by
      field_simp
    rw [hstep]
    exact alg_e1 c d α hrel
  have e2 : b^2 * ((1 + a/b*(1/(1+3*α)))*(1 + a/b*((4+α)/(7+2*α)))) * ((7+2*α)*(4+3*α)*(1+3*α))
      = ((a+2*b)*α + (4*a+7*b))*((a+2*b)*(3*α) + (4*a+7*b)) := by
    have hstep : b^2 * ((1 + a/b*(1/(1+3*α)))*(1 + a/b*((4+α)/(7+2*α)))) * ((7+2*α)*(4+3*α)*(1+3*α))
        = (b*(1+3*α)+a)*(4+3*α)*(b*(7+2*α)+a*(4+α)) := by
      field_simp
    rw [hstep]
    exact alg_e2 a b α hrel
  have hq' : (269/1000:ℝ)*((1 + c/d*α)*(1 + c/d*(1/(3+α))))*d^2
      < b^2*((1 + a/b*(1/(1+3*α)))*(1 + a/b*((4+α)/(7+2*α)))) := by
    rw [div_lt_div_iff₀ hV hd2] at hq
    exact hq
  have hL : (269/1000:ℝ)*((1 + c/d*α)*(1 + c/d*(1/(3+α))))*d^2*(((7+2*α)*(4+3*α)*(1+3*α))*(3+α))
      = (269/1000:ℝ)*(α * ((d*α + (c+3*d))*(d*(3*α) + (c+3*d))))*((7+2*α)*(4+3*α)*(1+3*α)) := by
    linear_combination ((269/1000:ℝ)*((7+2*α)*(4+3*α)*(1+3*α))) * e1
  have hR : b^2*((1 + a/b*(1/(1+3*α)))*(1 + a/b*((4+α)/(7+2*α))))*(((7+2*α)*(4+3*α)*(1+3*α))*(3+α))
      = (((a+2*b)*α + (4*a+7*b))*((a+2*b)*(3*α) + (4*a+7*b)))*(3+α) := by
    linear_combination (3+α) * e2
  have h1 : (269/1000:ℝ)*(α * ((d*α + (c+3*d))*(d*(3*α) + (c+3*d))))*((7+2*α)*(4+3*α)*(1+3*α))
      < (((a+2*b)*α + (4*a+7*b))*((a+2*b)*(3*α) + (4*a+7*b)))*(3+α) := by
    rw [← hL, ← hR]
    exact mul_lt_mul_of_pos_right hq' (mul_pos hM h3a)
  have h2 : (7/5:ℝ)*(3+α)*((d*α + (c+3*d))*(d*(3*α) + (c+3*d)))
      < (269/1000)*(α*((7+2*α)*(4+3*α)*(1+3*α)))*((d*α + (c+3*d))*(d*(3*α) + (c+3*d))) :=
    mul_lt_mul_of_pos_right hc2 (mul_pos hPa hPb)
  have h3 : ((7/5:ℝ)*((d*α + (c+3*d))*(d*(3*α) + (c+3*d))))*(3+α)
      < (((a+2*b)*α + (4*a+7*b))*((a+2*b)*(3*α) + (4*a+7*b)))*(3+α) := by
    nlinarith [h1, h2]
  exact lt_of_mul_lt_mul_right h3 h3a.le


end M7JEC

open M7JEC

theorem solution (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (hc : (lowerTheta 66-lowerTheta 63)/(lowerTheta 90-lowerTheta 3) < (253/1000:ℝ) ∧ (7/5:ℝ)*(lowerTheta 68-lowerTheta 65)/(lowerTheta 28-lowerTheta 1) < (269/1000:ℝ) ∧ lowerTheta 3 < lowerTheta 30 ∧ lowerTheta 30 < lowerTheta 63 ∧ lowerTheta 63 < lowerTheta 66 ∧ lowerTheta 66 < lowerTheta 90 ∧ lowerTheta 65 < lowerTheta 68 ∧ lowerTheta 1 < lowerTheta 28 ∧ (19/5:ℝ)*(253/1000)*(26/25)<1 ∧ (269/1000:ℝ)<(253/1000)*(133/125)) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) (hq : lowerJEqualQBounds p) : lowerJEqualContact p := by
  classical
  have hnorm : lowerNormalize p = p := by simp only [lowerNormalize, if_pos hwide]
  have hpar : p.1.length % 2 = p.2.length % 2 := by unfold lowerMixed at hp; omega
  -- constants
  have h21 : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h21n : (0:ℝ) ≤ Real.sqrt 21 := Real.sqrt_nonneg 21
  have h21b : (4:ℝ) < Real.sqrt 21 := by nlinarith
  have halpha : lowerAlpha = (Real.sqrt 21 - 3)/6 := rfl
  have hbeta : lowerBeta = (Real.sqrt 21 - 3)/2 := rfl
  have hab : lowerBeta = 3*lowerAlpha := by rw [halpha, hbeta]; ring
  have hA0 : (0:ℝ) < lowerAlpha := by rw [halpha]; linarith
  have hrel : 3*lowerAlpha^2 + 3*lowerAlpha = 1 := by rw [halpha]; nlinarith [h21]
  have hB0 : (0:ℝ) < lowerBeta := by rw [hab]; linarith
  have hBA : lowerAlpha < lowerBeta := by rw [hab]; linarith
  -- theta facts
  have o1 : lowerTheta 3 < lowerTheta 30 := hc.2.2.1
  have o2 : lowerTheta 30 < lowerTheta 63 := hc.2.2.2.1
  have o3 : lowerTheta 63 < lowerTheta 66 := hc.2.2.2.2.1
  have o4 : lowerTheta 66 < lowerTheta 90 := hc.2.2.2.2.2.1
  have o5 : lowerTheta 65 < lowerTheta 68 := hc.2.2.2.2.2.2.1
  have o6 : lowerTheta 1 < lowerTheta 28 := hc.2.2.2.2.2.2.2.1
  have htau0 : (0:ℝ) ≤ lowerTau := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3n : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    unfold lowerTau; nlinarith
  have t3 : (0:ℝ) ≤ lowerTheta 3 := by
    show (0:ℝ) ≤ prefixEval [3] lowerTau
    exact pe_nonneg _ _ htau0
  have t63 : (0:ℝ) ≤ lowerTheta 63 := by linarith
  have t66 : (0:ℝ) ≤ lowerTheta 66 := by linarith
  have t90 : (0:ℝ) ≤ lowerTheta 90 := by linarith
  have t1 : lowerTheta 1 = lowerAlpha := rfl
  have t1n : (0:ℝ) ≤ lowerTheta 1 := by rw [t1]; linarith
  have t28 : lowerTheta 28 = 1/(3+lowerAlpha) := rfl
  have t28n : (0:ℝ) ≤ lowerTheta 28 := by linarith
  have t65 : lowerTheta 65 = 1/(1+lowerBeta) := by
    show prefixEval [1] lowerBeta = 1/(1+lowerBeta)
    norm_num [prefixEval]
  have t65n : (0:ℝ) ≤ lowerTheta 65 := by
    show (0:ℝ) ≤ prefixEval [1] lowerBeta
    exact pe_nonneg _ _ (le_of_lt hB0)
  have t68n : (0:ℝ) ≤ lowerTheta 68 := by linarith
  -- continuant denominators
  have hD1 : (0:ℝ) < ((lowerCD p.1).2 : ℝ) := by exact_mod_cast cd_pos p.1
  have hD2 : (0:ℝ) < ((lowerCD p.2).2 : ℝ) := by exact_mod_cast cd_pos p.2
  have hC1 : (0:ℝ) ≤ ((lowerCD p.1).1 : ℝ) := Nat.cast_nonneg _
  have hC2 : (0:ℝ) ≤ ((lowerCD p.2).1 : ℝ) := Nat.cast_nonneg _
  have hr1 : (0:ℝ) ≤ lowerRatio p.1 := div_nonneg hC1 (le_of_lt hD1)
  have hr2 : (0:ℝ) ≤ lowerRatio p.2 := div_nonneg hC2 (le_of_lt hD2)
  have hone : ∀ (w : List ℕ+) (x : ℝ), ((lowerCD w).1 : ℝ)*x + ((lowerCD w).2 : ℝ)
      = ((lowerCD w).2 : ℝ) * (1 + lowerRatio w * x) := by
    intro w x
    have hd : ((lowerCD w).2:ℝ) ≠ 0 := by
      have : (0:ℝ) < ((lowerCD w).2:ℝ) := by exact_mod_cast cd_pos w
      exact this.ne'
    rw [lowerRatio]; field_simp; ring
  have hscale : lowerScale p = ((lowerCD p.1).2:ℝ)^2/((lowerCD p.2).2:ℝ)^2 := rfl
  have hu1 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 63 := by
    have := mul_nonneg hr1 t63; linarith
  have hu2 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 66 := by
    have := mul_nonneg hr1 t66; linarith
  have hv1 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 3 := by
    have := mul_nonneg hr2 t3; linarith
  have hv2 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 90 := by
    have := mul_nonneg hr2 t90; linarith
  have hw1 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 65 := by
    have := mul_nonneg hr1 t65n; linarith
  have hw2 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 68 := by
    have := mul_nonneg hr1 t68n; linarith
  have hz1 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 1 := by
    have := mul_nonneg hr2 t1n; linarith
  have hz2 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 28 := by
    have := mul_nonneg hr2 t28n; linarith
  refine ⟨?_, ?_⟩
  · -- first clause: the contact inequality
    have hq1 : (253/1000:ℝ) * ((1 + lowerRatio p.2 * lowerTheta 3)*(1 + lowerRatio p.2 * lowerTheta 90))
        * ((lowerCD p.2).2:ℝ)^2
        < ((lowerCD p.1).2:ℝ)^2 * ((1 + lowerRatio p.1 * lowerTheta 63)*(1 + lowerRatio p.1 * lowerTheta 66)) := by
      have h := hq.1
      rw [hnorm, hscale, div_lt_div_iff₀ (mul_pos hu1 hu2) (pow_pos hD2 2)] at h
      exact h
    have h903 : (0:ℝ) < lowerTheta 90 - lowerTheta 3 := by linarith
    have hcc : lowerTheta 66 - lowerTheta 63 < (253/1000)*(lowerTheta 90 - lowerTheta 3) := by
      have h := hc.1; rw [div_lt_iff₀ h903] at h; linarith
    have hP : (0:ℝ) < ((lowerCD p.2).2:ℝ)^2 * ((1+lowerRatio p.2*lowerTheta 3)*(1+lowerRatio p.2*lowerTheta 90)) :=
      mul_pos (pow_pos hD2 2) (mul_pos hv1 hv2)
    have hX : (0:ℝ) < (((lowerCD p.1).2:ℝ)*(1+lowerRatio p.1*lowerTheta 63))
        * (((lowerCD p.1).2:ℝ)*(1+lowerRatio p.1*lowerTheta 66)) :=
      mul_pos (mul_pos hD1 hu1) (mul_pos hD1 hu2)
    have hY : (0:ℝ) < (((lowerCD p.2).2:ℝ)*(1+lowerRatio p.2*lowerTheta 90))
        * (((lowerCD p.2).2:ℝ)*(1+lowerRatio p.2*lowerTheta 3)) :=
      mul_pos (mul_pos hD2 hv2) (mul_pos hD2 hv1)
    have hkey : (0:ℝ) < (lowerTheta 63 - lowerTheta 66)
          / ((((lowerCD p.1).2:ℝ)*(1+lowerRatio p.1*lowerTheta 63))
             * (((lowerCD p.1).2:ℝ)*(1+lowerRatio p.1*lowerTheta 66)))
        + (lowerTheta 90 - lowerTheta 3)
          / ((((lowerCD p.2).2:ℝ)*(1+lowerRatio p.2*lowerTheta 90))
             * (((lowerCD p.2).2:ℝ)*(1+lowerRatio p.2*lowerTheta 3))) := by
      rw [div_add_div _ _ (ne_of_gt hX) (ne_of_gt hY)]
      apply div_pos _ (mul_pos hX hY)
      have s1 := mul_lt_mul_of_pos_right hcc hP
      have s2 := mul_lt_mul_of_pos_left hq1 h903
      linarith [s1, s2]
    have hd1 := pe_diff p.1 (lowerTheta 63) (lowerTheta 66) t63 t66
    have hd2 := pe_diff p.2 (lowerTheta 90) (lowerTheta 3) t90 t3
    rw [hone p.1 (lowerTheta 63), hone p.1 (lowerTheta 66)] at hd1
    rw [hone p.2 (lowerTheta 90), hone p.2 (lowerTheta 3)] at hd2
    rw [sign_eq p.2.length p.1.length hpar.symm] at hd2
    have hsq : ((-1:ℝ)^p.1.length)*((-1:ℝ)^p.1.length) = 1 := by
      rcases Nat.even_or_odd p.1.length with h|h
      · rw [h.neg_one_pow]; norm_num
      · rw [h.neg_one_pow]; norm_num
    have hexp : lowerJActual p (lowerTheta 63) (lowerTheta 90) - lowerJActual p (lowerTheta 66) (lowerTheta 3)
        = (prefixEval p.1 (lowerTheta 63) - prefixEval p.1 (lowerTheta 66))
          + (prefixEval p.2 (lowerTheta 90) - prefixEval p.2 (lowerTheta 3)) := by
      simp only [lowerJActual, hnorm]; ring
    have gen : ∀ (σ A B X Y : ℝ), σ*σ = 1 → 0 < A/X + B/Y → 0 < σ * (σ*A/X + σ*B/Y) := by
      intro σ A B X Y hs h
      have he : σ * (σ*A/X + σ*B/Y) = (σ*σ)*(A/X) + (σ*σ)*(B/Y) := by ring
      rw [he, hs]; linarith
    rw [hnorm, hexp, hd1, hd2]
    exact gen _ _ _ _ _ hsq hkey
  · -- second clause
    have hbma : (0:ℝ) < lowerBeta - lowerAlpha := by linarith
    have n3 : (0:ℝ) < 3 + lowerAlpha := by linarith
    have n4 : (0:ℝ) < 4 + lowerAlpha := by linarith
    have n7 : (0:ℝ) < 7 + 2*lowerAlpha := by linarith
    have n1b : (0:ℝ) < 1 + lowerBeta := by linarith
    have n4b : (0:ℝ) < 4 + lowerBeta := by linarith
    -- closed form for theta 68
    have ht68 : lowerTheta 68 = (4+lowerAlpha)/(7+2*lowerAlpha) := by
      have e0 : lowerTheta 68 = prefixEval [1,1,3] lowerAlpha := rfl
      have e1 : prefixEval ([1,1,3] : List ℕ+) lowerAlpha
          = 1/(1 + 1/(1 + 1/(3+lowerAlpha))) := by
        norm_num [prefixEval]
      rw [e0, e1]
      have q1 : (1:ℝ) + 1/(3+lowerAlpha) = (4+lowerAlpha)/(3+lowerAlpha) := by
        field_simp
        ring
      rw [q1, one_div_div]
      have q2 : (1:ℝ) + (3+lowerAlpha)/(4+lowerAlpha) = (7+2*lowerAlpha)/(4+lowerAlpha) := by
        field_simp; ring
      rw [q2, one_div_div]
    -- the constant inequality (7/5)(3+α) < (269/1000) α M
    have hT28 : (0:ℝ) < lowerTheta 28 - lowerTheta 1 := by linarith
    have hid28 : (3+lowerAlpha)*(lowerTheta 28 - lowerTheta 1) = 2*lowerAlpha^2 := by
      rw [t28, t1, mul_sub, mul_one_div, div_self (ne_of_gt n3)]
      linear_combination -hrel
    have g68 : lowerTheta 68 * (7+2*lowerAlpha) = 4 + lowerAlpha := by
      rw [ht68]; field_simp
    have g65 : lowerTheta 65 * (1+lowerBeta) = 1 := by
      rw [t65]; field_simp
    have hid68 : ((7+2*lowerAlpha)*(4+lowerBeta)*(1+lowerBeta))*(lowerTheta 68 - lowerTheta 65)
        = 2*lowerAlpha := by
      rw [hab] at g65 ⊢
      linear_combination ((4+3*lowerAlpha)*(1+3*lowerAlpha))*g68
        - ((7+2*lowerAlpha)*(4+3*lowerAlpha))*g65 + (3*(lowerAlpha+4))*hrel
    have hMp : (0:ℝ) < (7+2*lowerAlpha)*(4+lowerBeta)*(1+lowerBeta) :=
      mul_pos (mul_pos n7 n4b) n1b
    have haM : (0:ℝ) < lowerAlpha*((7+2*lowerAlpha)*(4+lowerBeta)*(1+lowerBeta)) := mul_pos hA0 hMp
    have e68 : lowerAlpha*(((7+2*lowerAlpha)*(4+lowerBeta)*(1+lowerBeta))*(lowerTheta 68 - lowerTheta 65))
        = 2*lowerAlpha^2 := by rw [hid68]; ring
    have hc2 : (7/5:ℝ)*(3+lowerAlpha)
        < (269/1000)*(lowerAlpha*((7+2*lowerAlpha)*(4+lowerBeta)*(1+lowerBeta))) := by
      have h := hc.2.1
      rw [div_lt_iff₀ hT28] at h
      have h2 := mul_lt_mul_of_pos_left h haM
      have h3 : (7/5:ℝ)*(3+lowerAlpha)*(lowerTheta 28 - lowerTheta 1)
          < (269/1000)*(lowerAlpha*((7+2*lowerAlpha)*(4+lowerBeta)*(1+lowerBeta)))
            *(lowerTheta 28 - lowerTheta 1) := by
        linarith [h2, hid28, e68]
      exact lt_of_mul_lt_mul_right h3 hT28.le
    -- continuant identities for the two appended words
    have cdu1 : (lowerCD (p.1 ++ [1,1,3])).1 = (lowerCD p.1).1 + 2*(lowerCD p.1).2 := by
      rw [cd_append]
      show (lowerCD p.1).2 + 1*((lowerCD p.1).1 + 1*(lowerCD p.1).2) = _
      ring
    have cdu2 : (lowerCD (p.1 ++ [1,1,3])).2 = 4*(lowerCD p.1).1 + 7*(lowerCD p.1).2 := by
      rw [cd_append]
      show ((lowerCD p.1).1 + 1*(lowerCD p.1).2)
            + 3*((lowerCD p.1).2 + 1*((lowerCD p.1).1 + 1*(lowerCD p.1).2)) = _
      ring
    have cdv1 : (lowerCD (p.2 ++ [3])).1 = (lowerCD p.2).2 := by rw [cd_append]; rfl
    have cdv2 : (lowerCD (p.2 ++ [3])).2 = (lowerCD p.2).1 + 3*(lowerCD p.2).2 := by
      rw [cd_append]; rfl
    -- the Q-bound hypothesis in explicit coordinates
    have hqq := hq.2
    rw [hnorm, hscale] at hqq
    simp only [lowerRatio, t1, t28, t65, ht68] at hqq
    have hrat1 : (0:ℝ) ≤ ((lowerCD p.1).1:ℝ)/((lowerCD p.1).2:ℝ) := div_nonneg hC1 hD1.le
    have k1 : (0:ℝ) < 1/(1+lowerBeta) := div_pos one_pos n1b
    have k2 : (0:ℝ) < (4+lowerAlpha)/(7+2*lowerAlpha) := div_pos n4 n7
    have hVpos : (0:ℝ) < (1 + ((lowerCD p.1).1:ℝ)/((lowerCD p.1).2:ℝ)*(1/(1+lowerBeta)))
        *(1 + ((lowerCD p.1).1:ℝ)/((lowerCD p.1).2:ℝ)*((4+lowerAlpha)/(7+2*lowerAlpha))) :=
      mul_pos (by linarith [mul_nonneg hrat1 k1.le]) (by linarith [mul_nonneg hrat1 k2.le])
    have key := clause2_core ((lowerCD p.1).1:ℝ) ((lowerCD p.1).2:ℝ)
      ((lowerCD p.2).1:ℝ) ((lowerCD p.2).2:ℝ) lowerAlpha lowerBeta hD1 hD2 hA0 hC1 hC2
      hab hrel hVpos hqq hc2
    -- conclude
    have hQa : (0:ℝ) < (((lowerCD p.1).1:ℝ)+2*((lowerCD p.1).2:ℝ))*lowerAlpha
        + (4*((lowerCD p.1).1:ℝ)+7*((lowerCD p.1).2:ℝ)) := by
      linarith [mul_nonneg hC1 hA0.le, mul_pos hD1 hA0]
    have hQb : (0:ℝ) < (((lowerCD p.1).1:ℝ)+2*((lowerCD p.1).2:ℝ))*lowerBeta
        + (4*((lowerCD p.1).1:ℝ)+7*((lowerCD p.1).2:ℝ)) := by
      linarith [mul_nonneg hC1 hB0.le, mul_pos hD1 hB0]
    have hPa : (0:ℝ) < ((lowerCD p.2).2:ℝ)*lowerAlpha
        + (((lowerCD p.2).1:ℝ)+3*((lowerCD p.2).2:ℝ)) := by
      linarith [mul_pos hD2 hA0]
    have hPb : (0:ℝ) < ((lowerCD p.2).2:ℝ)*lowerBeta
        + (((lowerCD p.2).1:ℝ)+3*((lowerCD p.2).2:ℝ)) := by
      linarith [mul_pos hD2 hB0]
    rw [hnorm, hw (p.1 ++ [1,1,3]), hw (p.2 ++ [3]), cdu1, cdu2, cdv1, cdv2]
    push_cast
    rw [← mul_div_assoc, div_lt_div_iff₀ (mul_pos hQa hQb) (mul_pos hPa hPb)]
    linarith [mul_lt_mul_of_pos_left key hbma]

