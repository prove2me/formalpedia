-- Prove2me | solution 1 for Freiman.lowerJ_equal_Q
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T17:33:23.504981+00:00
-- url     : https://prove2.me/submissions/f865b942-1f71-49eb-bb6a-d9b2dc10c4c4

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

open Freiman

namespace M7JQ

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

lemma cd_pos (w : List ℕ+) : 0 < (lowerCD w).2 := by
  induction w using List.reverseRecOn with
  | nil => exact Nat.one_pos
  | append_singleton w a ih =>
      have hcd : lowerCD (w ++ [a]) = ((lowerCD w).2, (lowerCD w).1 + (a:ℕ) * (lowerCD w).2) := by
        simp [lowerCD, List.foldl_append]
      rw [hcd]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos a.property ih) (Nat.le_add_left _ _)

lemma combine104 (N M X1 X2 d2 b2 : ℝ)
    (hM : 0 < M) (hX1 : 0 < X1) (hd2 : 0 < d2) (hb2 : 0 < b2)
    (h104 : X1*N < (26/25)*(M*X2))
    (hkey : d2*X2 < (19/5)*(b2*X1))
    (hcst : (19/5:ℝ)*(253/1000)*(26/25) < 1) :
    (253/1000:ℝ)*N*d2 < b2*M := by
  have p1 : ((253/1000:ℝ)*d2)*(X1*N) < ((253/1000:ℝ)*d2)*((26/25)*(M*X2)) :=
    mul_lt_mul_of_pos_left h104 (mul_pos (by norm_num) hd2)
  have p2 : ((253/1000:ℝ)*(26/25)*M)*(d2*X2) < ((253/1000:ℝ)*(26/25)*M)*((19/5)*(b2*X1)) :=
    mul_lt_mul_of_pos_left hkey (mul_pos (by norm_num) hM)
  have p3 : ((19/5:ℝ)*(253/1000)*(26/25))*(M*b2*X1) < 1*(M*b2*X1) :=
    mul_lt_mul_of_pos_right hcst (mul_pos (mul_pos hM hb2) hX1)
  have p4 : ((253/1000:ℝ)*N*d2)*X1 < (b2*M)*X1 := by linarith [p1, p2, p3]
  exact lt_of_mul_lt_mul_right p4 hX1.le

lemma combine1064 (N M N' M' d2 b2 : ℝ)
    (hM : 0 < M) (hM' : 0 < M') (hN' : 0 < N') (hd2 : 0 < d2)
    (h1064 : (133/125:ℝ)*(M*N') < M'*N)
    (hg1 : (253/1000:ℝ)*N*d2 < b2*M)
    (hcst : (269/1000:ℝ) < (253/1000)*(133/125)) :
    (269/1000:ℝ)*N'*d2 < b2*M' := by
  have q1 : ((253/1000:ℝ)*d2)*((133/125:ℝ)*(M*N')) < ((253/1000:ℝ)*d2)*(M'*N) :=
    mul_lt_mul_of_pos_left h1064 (mul_pos (by norm_num) hd2)
  have q2 : ((253/1000:ℝ)*N*d2)*M' < (b2*M)*M' := mul_lt_mul_of_pos_right hg1 hM'
  have q3 : (269/1000:ℝ)*(d2*N'*M) < ((253/1000:ℝ)*(133/125))*(d2*N'*M) :=
    mul_lt_mul_of_pos_right hcst (mul_pos (mul_pos hd2 hN') hM)
  have q4 : ((269/1000:ℝ)*N'*d2)*M < (b2*M')*M := by linarith [q1, q2, q3]
  exact lt_of_mul_lt_mul_right q4 hM.le

end M7JQ

open M7JQ

theorem solution (hw : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2))) (hc : (lowerTheta 66-lowerTheta 63)/(lowerTheta 90-lowerTheta 3) < (253/1000:ℝ) ∧ (7/5:ℝ)*(lowerTheta 68-lowerTheta 65)/(lowerTheta 28-lowerTheta 1) < (269/1000:ℝ) ∧ lowerTheta 3 < lowerTheta 30 ∧ lowerTheta 30 < lowerTheta 63 ∧ lowerTheta 63 < lowerTheta 66 ∧ lowerTheta 66 < lowerTheta 90 ∧ lowerTheta 65 < lowerTheta 68 ∧ lowerTheta 1 < lowerTheta 28 ∧ (19/5:ℝ)*(253/1000)*(26/25)<1 ∧ (269/1000:ℝ)<(253/1000)*(133/125)) (hpoly : ∀ r s : ℝ, r ∈ Set.Icc (1/4:ℝ) (4/5) → s ∈ Set.Icc (1/4:ℝ) (4/5) → lowerJPolyFacts r s) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) : lowerJEqualQBounds p := by
  classical
  have hnorm : lowerNormalize p = p := by simp only [lowerNormalize, if_pos hwide]
  -- basic constants
  have h21 : Real.sqrt 21 ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  have h21n : (0:ℝ) ≤ Real.sqrt 21 := Real.sqrt_nonneg 21
  have h21b : (4:ℝ) < Real.sqrt 21 := by nlinarith
  have halpha : lowerAlpha = (Real.sqrt 21 - 3)/6 := rfl
  have hbeta : lowerBeta = (Real.sqrt 21 - 3)/2 := rfl
  have hA0 : (0:ℝ) < lowerAlpha := by rw [halpha]; linarith
  have hB0 : (0:ℝ) < lowerBeta := by rw [hbeta]; linarith
  have hBA : lowerAlpha < lowerBeta := by rw [halpha, hbeta]; linarith
  have hbma : (0:ℝ) < lowerBeta - lowerAlpha := by linarith
  have htau0 : (0:ℝ) ≤ lowerTau := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h3n : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    unfold lowerTau; nlinarith
  -- theta facts
  have o1 : lowerTheta 3 < lowerTheta 30 := hc.2.2.1
  have o2 : lowerTheta 30 < lowerTheta 63 := hc.2.2.2.1
  have o3 : lowerTheta 63 < lowerTheta 66 := hc.2.2.2.2.1
  have o4 : lowerTheta 66 < lowerTheta 90 := hc.2.2.2.2.2.1
  have o5 : lowerTheta 65 < lowerTheta 68 := hc.2.2.2.2.2.2.1
  have o6 : lowerTheta 1 < lowerTheta 28 := hc.2.2.2.2.2.2.2.1
  have hcst1 : (19/5:ℝ)*(253/1000)*(26/25) < 1 := hc.2.2.2.2.2.2.2.2.1
  have hcst2 : (269/1000:ℝ) < (253/1000)*(133/125) := hc.2.2.2.2.2.2.2.2.2
  have t1 : lowerTheta 1 = lowerAlpha := rfl
  have t95 : lowerTheta 95 = lowerBeta := rfl
  have t3 : (0:ℝ) ≤ lowerTheta 3 := by
    show (0:ℝ) ≤ prefixEval [3] lowerTau
    exact pe_nonneg _ _ htau0
  have t63 : (0:ℝ) ≤ lowerTheta 63 := by linarith
  have t66 : (0:ℝ) ≤ lowerTheta 66 := by linarith
  have t90 : (0:ℝ) ≤ lowerTheta 90 := by linarith
  have t65 : (0:ℝ) ≤ lowerTheta 65 := by
    show (0:ℝ) ≤ prefixEval [1] lowerBeta
    exact pe_nonneg _ _ hB0.le
  have t68 : (0:ℝ) ≤ lowerTheta 68 := by linarith
  have t1n : (0:ℝ) ≤ lowerTheta 1 := by rw [t1]; linarith
  have t28 : (0:ℝ) ≤ lowerTheta 28 := by linarith
  have t95n : (0:ℝ) ≤ lowerTheta 95 := by rw [t95]; linarith
  -- continuants
  have hD1 : (0:ℝ) < ((lowerCD p.1).2 : ℝ) := by exact_mod_cast cd_pos p.1
  have hD2 : (0:ℝ) < ((lowerCD p.2).2 : ℝ) := by exact_mod_cast cd_pos p.2
  have hC1 : (0:ℝ) ≤ ((lowerCD p.1).1 : ℝ) := Nat.cast_nonneg _
  have hC2 : (0:ℝ) ≤ ((lowerCD p.2).1 : ℝ) := Nat.cast_nonneg _
  have hb1 : (1/4:ℝ) ≤ lowerRatio p.1 := hb.1
  have hb2 : lowerRatio p.1 ≤ (4/5:ℝ) := hb.2.1
  have hb3 : (1/4:ℝ) ≤ lowerRatio p.2 := hb.2.2.1
  have hb4 : lowerRatio p.2 ≤ (4/5:ℝ) := hb.2.2.2
  have hr1 : (0:ℝ) ≤ lowerRatio p.1 := by linarith
  have hr2 : (0:ℝ) ≤ lowerRatio p.2 := by linarith
  have hone : ∀ (w : List ℕ+) (x : ℝ), ((lowerCD w).1 : ℝ)*x + ((lowerCD w).2 : ℝ)
      = ((lowerCD w).2 : ℝ) * (1 + lowerRatio w * x) := by
    intro w x
    have hd : ((lowerCD w).2:ℝ) ≠ 0 := by
      have : (0:ℝ) < ((lowerCD w).2:ℝ) := by exact_mod_cast cd_pos w
      exact this.ne'
    rw [lowerRatio]; field_simp; ring
  have hscale : lowerScale p = ((lowerCD p.1).2:ℝ)^2/((lowerCD p.2).2:ℝ)^2 := rfl
  -- positivity of all the factors
  have f1a : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 1 := by
    have := mul_nonneg hr1 t1n; linarith
  have f1b : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 95 := by
    have := mul_nonneg hr1 t95n; linarith
  have f2a : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 1 := by
    have := mul_nonneg hr2 t1n; linarith
  have f2b : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 95 := by
    have := mul_nonneg hr2 t95n; linarith
  have g1 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 3 := by
    have := mul_nonneg hr2 t3; linarith
  have g2 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 90 := by
    have := mul_nonneg hr2 t90; linarith
  have m1 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 63 := by
    have := mul_nonneg hr1 t63; linarith
  have m2 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 66 := by
    have := mul_nonneg hr1 t66; linarith
  have n1 : (0:ℝ) < 1 + lowerRatio p.2 * lowerTheta 28 := by
    have := mul_nonneg hr2 t28; linarith
  have k1 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 65 := by
    have := mul_nonneg hr1 t65; linarith
  have k2 : (0:ℝ) < 1 + lowerRatio p.1 * lowerTheta 68 := by
    have := mul_nonneg hr1 t68; linarith
  -- widths in continuant coordinates
  have hE1 : (0:ℝ) < ((lowerCD p.1).2:ℝ)^2
      * ((1 + lowerRatio p.1 * lowerTheta 1)*(1 + lowerRatio p.1 * lowerTheta 95)) :=
    mul_pos (pow_pos hD1 2) (mul_pos f1a f1b)
  have hE2 : (0:ℝ) < ((lowerCD p.2).2:ℝ)^2
      * ((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 95)) :=
    mul_pos (pow_pos hD2 2) (mul_pos f2a f2b)
  have hW1 : lowerWidth p.1 = (lowerBeta-lowerAlpha)/(((lowerCD p.1).2:ℝ)^2
      * ((1 + lowerRatio p.1 * lowerTheta 1)*(1 + lowerRatio p.1 * lowerTheta 95))) := by
    rw [hw p.1, hone p.1 lowerAlpha, hone p.1 lowerBeta, t1, t95]
    congr 1
    ring
  have hW2 : lowerWidth p.2 = (lowerBeta-lowerAlpha)/(((lowerCD p.2).2:ℝ)^2
      * ((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 95))) := by
    rw [hw p.2, hone p.2 lowerAlpha, hone p.2 lowerBeta, t1, t95]
    congr 1
    ring
  have hkey : ((lowerCD p.2).2:ℝ)^2
        * ((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 95))
      < (19/5) * (((lowerCD p.1).2:ℝ)^2
        * ((1 + lowerRatio p.1 * lowerTheta 1)*(1 + lowerRatio p.1 * lowerTheta 95))) := by
    rw [hW1, hW2, ← mul_div_assoc, div_lt_div_iff₀ hE1 hE2] at hratio
    have h' : (lowerBeta-lowerAlpha) * (((lowerCD p.2).2:ℝ)^2
          * ((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 95)))
        < (lowerBeta-lowerAlpha) * ((19/5) * (((lowerCD p.1).2:ℝ)^2
          * ((1 + lowerRatio p.1 * lowerTheta 1)*(1 + lowerRatio p.1 * lowerTheta 95)))) := by
      linarith [hratio]
    exact lt_of_mul_lt_mul_left h' hbma.le
  -- polynomial facts on the box
  have hpf := hpoly (lowerRatio p.1) (lowerRatio p.2)
    (Set.mem_Icc.mpr ⟨hb1, hb2⟩) (Set.mem_Icc.mpr ⟨hb3, hb4⟩)
  have h104 := hpf.2.2.1
  have h1064 := hpf.2.2.2
  rw [lowerJProd104, div_lt_iff₀ (by positivity)] at h104
  rw [lowerJProd1064, lt_div_iff₀ (by positivity)] at h1064
  -- the two goals
  have goal1 : (253/1000:ℝ)*((1 + lowerRatio p.2 * lowerTheta 3)*(1 + lowerRatio p.2 * lowerTheta 90))
        * ((lowerCD p.2).2:ℝ)^2
      < ((lowerCD p.1).2:ℝ)^2
        * ((1 + lowerRatio p.1 * lowerTheta 63)*(1 + lowerRatio p.1 * lowerTheta 66)) := by
    refine combine104
      ((1 + lowerRatio p.2 * lowerTheta 3)*(1 + lowerRatio p.2 * lowerTheta 90))
      ((1 + lowerRatio p.1 * lowerTheta 63)*(1 + lowerRatio p.1 * lowerTheta 66))
      ((1 + lowerRatio p.1 * lowerTheta 1)*(1 + lowerRatio p.1 * lowerTheta 95))
      ((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 95))
      (((lowerCD p.2).2:ℝ)^2) (((lowerCD p.1).2:ℝ)^2)
      (mul_pos m1 m2) (mul_pos f1a f1b) (pow_pos hD2 2)
      (pow_pos hD1 2) ?_ ?_ hcst1
    · linarith [h104]
    · linarith [hkey]
  have goal2 : (269/1000:ℝ)*((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 28))
        * ((lowerCD p.2).2:ℝ)^2
      < ((lowerCD p.1).2:ℝ)^2
        * ((1 + lowerRatio p.1 * lowerTheta 65)*(1 + lowerRatio p.1 * lowerTheta 68)) := by
    refine combine1064
      ((1 + lowerRatio p.2 * lowerTheta 3)*(1 + lowerRatio p.2 * lowerTheta 90))
      ((1 + lowerRatio p.1 * lowerTheta 63)*(1 + lowerRatio p.1 * lowerTheta 66))
      ((1 + lowerRatio p.2 * lowerTheta 1)*(1 + lowerRatio p.2 * lowerTheta 28))
      ((1 + lowerRatio p.1 * lowerTheta 65)*(1 + lowerRatio p.1 * lowerTheta 68))
      (((lowerCD p.2).2:ℝ)^2) (((lowerCD p.1).2:ℝ)^2)
      (mul_pos m1 m2) (mul_pos k1 k2) (mul_pos f2a n1)
      (pow_pos hD2 2) ?_ goal1 hcst2
    · linarith [h1064]
  refine ⟨?_, ?_⟩
  · rw [hnorm, hscale, div_lt_div_iff₀ (mul_pos m1 m2) (pow_pos hD2 2)]
    exact goal1
  · rw [hnorm, hscale, div_lt_div_iff₀ (mul_pos k1 k2) (pow_pos hD2 2)]
    exact goal2
