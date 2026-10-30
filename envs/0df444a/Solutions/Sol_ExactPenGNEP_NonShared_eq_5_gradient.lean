-- Prove2me | solution 1 for ExactPenGNEP.NonShared.eq_5_gradient
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:44:08.717118+00:00
-- url     : https://prove2.me/submissions/8746cc96-75cf-4499-8994-38eac2f0ed15

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync ExactPenGNEP.NonShared Filter Topology Asymptotics

lemma epg_hasDerivAt_maxpos_rpow {q : ℝ} (hq : 1 < q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (max s 0) ^ q) (q * (max t 0) ^ (q - 1)) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hev : (fun s : ℝ => (max s 0) ^ q) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [max_eq_right (le_of_lt hs), Real.zero_rpow (by linarith)]
    rw [max_eq_right ht.le, Real.zero_rpow (by linarith), mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst ht
    rw [max_self, Real.zero_rpow (by linarith), mul_zero]
    have h1 := hasDerivAt_abs_rpow (0 : ℝ) hq
    simp only [mul_zero] at h1
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h1 ⊢
    simp only [zero_add, abs_zero, Real.zero_rpow (by linarith : q ≠ 0), sub_zero, max_self,
      smul_zero] at h1 ⊢
    refine IsBigO.trans_isLittleO ?_ h1
    refine IsBigO.of_bound 1 (Eventually.of_forall fun s => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le (le_abs_self _) (abs_nonneg _))
      (by linarith)
  · have hev : (fun s : ℝ => (max s 0) ^ q) =ᶠ[𝓝 t] fun s => s ^ q := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt hs)]
    rw [max_eq_left ht.le]
    exact (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).congr_of_eventuallyEq hev

lemma epg_hasDerivAt_abs_rpow' {q : ℝ} (hq : 1 < q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => |s| ^ q) (q * (|t| ^ (q - 1) * Real.sign t)) t := by
  convert hasDerivAt_abs_rpow t hq using 1
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]
    have hpos : 0 < -t := by linarith
    have : (-t) ^ (q - 1) = (-t) ^ (q - 2) * (-t) := by
      rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
    rw [this]; ring
  · subst ht; simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht]
    have : t ^ (q - 1) = t ^ (q - 2) * t := by
      rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
    rw [this]; ring

theorem solution {k m p : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin k) → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin k) → ℝ) (q : ℝ) (x : EuclideanSpace ℝ (Fin k))
    (hg : ∀ i, Differentiable ℝ (g i)) (hh : ∀ j, Differentiable ℝ (h j)) (hq : 1 < q)
    (hx : x ∉ {y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0}) :
    HasFDerivAt (lqRes g h q)
      ((1 / lqRes g h q x ^ (q - 1)) •
        (∑ i, (max (g i x) 0) ^ (q - 1) • fderiv ℝ (g i) x +
          ∑ j, (|h j x| ^ (q - 1) * Real.sign (h j x)) • fderiv ℝ (h j) x)) x := by
  set S : EuclideanSpace ℝ (Fin k) → ℝ :=
    fun y => ∑ i, (max (g i y) 0) ^ q + ∑ j, |h j y| ^ q with hS_def
  set L := ∑ i, (max (g i x) 0) ^ (q - 1) • fderiv ℝ (g i) x +
          ∑ j, (|h j x| ^ (q - 1) * Real.sign (h j x)) • fderiv ℝ (h j) x with hL
  have hSd : HasFDerivAt S (q • L) x := by
    have h1 : HasFDerivAt (fun y => ∑ i, (max (g i y) 0) ^ q)
        (∑ i, (q * (max (g i x) 0) ^ (q - 1)) • fderiv ℝ (g i) x) x := by
      apply HasFDerivAt.fun_sum
      intro i _
      exact (epg_hasDerivAt_maxpos_rpow hq (g i x)).comp_hasFDerivAt x ((hg i) x).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ∑ j, |h j y| ^ q)
        (∑ j, (q * (|h j x| ^ (q - 1) * Real.sign (h j x))) • fderiv ℝ (h j) x) x := by
      apply HasFDerivAt.fun_sum
      intro j _
      exact (epg_hasDerivAt_abs_rpow' hq (h j x)).comp_hasFDerivAt x ((hh j) x).hasFDerivAt
    refine (h1.add h2).congr_fderiv ?_
    rw [hL, smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [smul_smul]
  have hSpos : 0 < S x := by
    simp only [Set.mem_ofPred_eq, not_and, not_forall] at hx
    by_cases hgi : ∃ i, 0 < g i x
    · obtain ⟨i, hi⟩ := hgi
      have hterm : 0 < (max (g i x) 0) ^ q := by
        rw [max_eq_left hi.le]; exact Real.rpow_pos_of_pos hi _
      have hle : (max (g i x) 0) ^ q ≤ ∑ i, (max (g i x) 0) ^ q :=
        Finset.single_le_sum (f := fun i => (max (g i x) 0) ^ q)
          (fun i _ => Real.rpow_nonneg (le_max_right _ _) _) (Finset.mem_univ i)
      have h2 : 0 ≤ ∑ j, |h j x| ^ q :=
        Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      simp only [hS_def]; linarith
    · push Not at hgi
      obtain ⟨j, hj⟩ := hx hgi
      have hterm : 0 < |h j x| ^ q := Real.rpow_pos_of_pos (abs_pos.mpr hj) _
      have hle : |h j x| ^ q ≤ ∑ j, |h j x| ^ q :=
        Finset.single_le_sum (f := fun j => |h j x| ^ q)
          (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ j)
      have h1 : 0 ≤ ∑ i, (max (g i x) 0) ^ q :=
        Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (le_max_right _ _) _)
      simp only [hS_def]; linarith
  have hR := hSd.rpow_const (p := 1 / q) (Or.inl hSpos.ne')
  have hlq : lqRes g h q = fun y => S y ^ (1 / q) := rfl
  rw [hlq]
  refine hR.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  have hq0 : 0 < q := by linarith
  have e1 : (S x ^ (1 / q)) ^ (q - 1) = S x ^ (1 - 1 / q) := by
    rw [← Real.rpow_mul hSpos.le]; congr 1; field_simp
  have e2 : S x ^ (1 / q - 1) = (S x ^ (1 - 1 / q))⁻¹ := by
    rw [← Real.rpow_neg hSpos.le]; congr 1; ring
  rw [e1, e2]
  field_simp
