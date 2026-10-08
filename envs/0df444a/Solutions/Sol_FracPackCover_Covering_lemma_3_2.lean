-- Prove2me | solution 1 for FracPackCover.Covering.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:42:31.444159+00:00
-- url     : https://prove2.me/submissions/93750efe-da3e-40a9-973f-998e5a25b4c9

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

open FracPackCover.Covering

private lemma exp_tail (a δ r l : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (had : 1 / 2 ≤ a * δ) :
    (r - (l + δ)) * Real.exp (-(a * r)) ≤
      2 * δ * Real.exp (-(a * (l + δ))) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (a * (r - (l + δ)))
  have he : Real.exp (-1) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
  have h1 : (a * (r - (l + δ))) * Real.exp (-(a * (r - (l + δ)))) ≤ 1 := h.trans he
  have hid : Real.exp (-(a * r)) =
      Real.exp (-(a * (r - (l + δ)))) * Real.exp (-(a * (l + δ))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hid]
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(a * (l + δ)))).le
  have h3 : (r - (l + δ)) *
      (Real.exp (-(a * (r - (l + δ)))) * Real.exp (-(a * (l + δ)))) ≤
        Real.exp (-(a * (l + δ))) / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [h2]
  have h4 : 1 / a ≤ 2 * δ := (div_le_iff₀ ha).mpr (by nlinarith)
  exact h3.trans (by simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-(a * (l + δ)))).le)

private lemma weighted_exp_bound {m : ℕ} [NeZero m] (r : Fin m → ℝ)
    (l ε a : ℝ) (hl : 0 < l) (hε : 0 < ε) (hε1 : ε < 1)
    (hmin : ∀ i, l ≤ r i) (hex : ∃ i, r i = l)
    (ha : 2 * l⁻¹ * ε⁻¹ * Real.log (4 * m * ε⁻¹) ≤ a) :
    (∑ i, r i * Real.exp (-(a * r i))) ≤
      (1 + ε) * l * ∑ i, Real.exp (-(a * r i)) := by
  let δ := ε * l / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  have ht : 2 ≤ 4 * (m : ℝ) * ε⁻¹ := by
    have hi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1.le
    nlinarith
  have ht0 : 0 < 4 * (m : ℝ) * ε⁻¹ := by positivity
  have hlog : (1 / 2 : ℝ) ≤ Real.log (4 * m * ε⁻¹) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hx := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) ht
    norm_num at h2
    linarith
  have had : Real.log (4 * m * ε⁻¹) ≤ a * δ := by
    have hh := mul_le_mul_of_nonneg_right ha hδ.le
    have hid : (2 * l⁻¹ * ε⁻¹ * Real.log (4 * m * ε⁻¹)) * δ =
        Real.log (4 * m * ε⁻¹) := by dsimp [δ]; field_simp
    rwa [hid] at hh
  have ha0 : 0 < a := by nlinarith
  have hsmall : Real.exp (-(a * δ)) ≤ ε / (4 * m) := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg had)
    rw [Real.exp_neg (Real.log _), Real.exp_log ht0] at hh
    convert hh using 1 <;> field_simp <;> ring
  let Z := ∑ i, Real.exp (-(a * r i))
  have hZ : Real.exp (-(a * l)) ≤ Z := by
    obtain ⟨i, hi⟩ := hex
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      (Real.exp_pos (-(a * r j))).le) (Finset.mem_univ i)
    simpa [hi, Z] using hh
  have hsum : (∑ i, (r i - (l + δ)) * Real.exp (-(a * r i))) ≤
      (m : ℝ) * (2 * δ * Real.exp (-(a * (l + δ)))) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      exp_tail a δ (r i) l ha0 hδ (hlog.trans had))
  have hid : Real.exp (-(a * (l + δ))) =
      Real.exp (-(a * l)) * Real.exp (-(a * δ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hid] at hsum
  have hh := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ (m : ℝ) * (2 * δ * Real.exp (-(a * l))) by positivity)
  have ht' : (m : ℝ) * (2 * δ * Real.exp (-(a * l)) * Real.exp (-(a * δ))) ≤
      δ * Real.exp (-(a * l)) := by
    have hid' : (m : ℝ) * (2 * δ * Real.exp (-(a * l))) * (ε / (4 * m)) =
        δ * Real.exp (-(a * l)) * (ε / 2) := by field_simp; ring
    rw [hid'] at hh
    calc
      _ = (m : ℝ) * (2 * δ * Real.exp (-(a * l))) * Real.exp (-(a * δ)) := by ring
      _ ≤ δ * Real.exp (-(a * l)) * (ε / 2) := hh
      _ ≤ δ * Real.exp (-(a * l)) := by
        have hhalf : ε / 2 ≤ 1 := by linarith
        simpa using mul_le_mul_of_nonneg_left hhalf
          (show 0 ≤ δ * Real.exp (-(a * l)) by positivity)
  have hlast := mul_le_mul_of_nonneg_left hZ hδ.le
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  have ht'' : (m : ℝ) * (2 * δ * (Real.exp (-(a * l)) * Real.exp (-(a * δ)))) ≤
      δ * Real.exp (-(a * l)) := by simpa only [mul_assoc] using ht'
  have htotal := hsum.trans ht''
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at htotal
  dsimp [δ] at htotal hlast
  dsimp [Z] at hlast hZ0 ⊢
  nlinarith

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b x)
    (ε α : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hα : 2 * (lam A b x)⁻¹ * ε⁻¹ * Real.log (4 * m * ε⁻¹) ≤ α) :
    C1 A b ε (lam A b x) (dualY A b α x) x := by
  have hmin (i : Fin m) : lam A b x ≤ rowVal A x i / b i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have hex : ∃ i : Fin m, rowVal A x i / b i = lam A b x := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i => rowVal A x i / b i)
    exact ⟨i, hi.symm⟩
  have h := weighted_exp_bound (fun i => rowVal A x i / b i)
    (lam A b x) ε α hlam hε hε1 hmin hex hα
  have hbi (i : Fin m) : b i ≠ 0 := (hdata.2.1 i).ne'
  unfold C1 yAx ytb dualY
  convert h using 1 <;> congr 1
  · funext i
    rw [← mul_div_assoc]
    ring
  · congr 1
    funext i
    rw [← mul_div_assoc]
    field_simp [hbi i]

#print axioms solution
