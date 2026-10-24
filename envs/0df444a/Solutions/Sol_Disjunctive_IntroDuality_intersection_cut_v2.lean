-- Prove2me | solution 1 for Disjunctive.IntroDuality.intersection_cut_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:30:18.11585+00:00
-- url     : https://prove2.me/submissions/ce9e9417-db63-467f-81a2-880e558e9d5c

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_IntersectionCut

namespace DK88
open Disjunctive.IntroDuality

lemma lam_pos {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (xbar r : ι → ℝ)
    (hx : xbar ∈ interior S) (l : ℝ) (hl : IsGreatest {t : ℝ | xbar + t • r ∈ S} l) : 0 < l := by
  have hc : Continuous (fun t : ℝ => xbar + t • r) := by fun_prop
  have h1 : ∀ᶠ t in nhds (0:ℝ), xbar + t • r ∈ S := by
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this (mem_interior_iff_mem_nhds.1 hx)
  have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), xbar + t • r ∈ S ∧ t ∈ Set.Ioi 0 :=
    (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ht, ht0⟩ := h2.exists
  exact lt_of_lt_of_le ht0 (hl.2 ht)

end DK88

open Disjunctive.IntroDuality in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (hIJ : Disjoint I J) (hcover : ∀ i : ι, i ∈ I ∨ i ∈ J)
    (abar : ι → ι → ℝ) (xbar : ι → ℝ) (PI S : Set (ι → ℝ))
    (hPIFree : PIFree S PI xbar)
    (hxbarJ : ∀ j ∈ J, xbar j = 0)
    (hPI_cone : ∀ x ∈ PI,
      (∀ i ∈ I, x i = xbar i - ∑ j ∈ J, abar i j * x j) ∧ ∀ j ∈ J, 0 ≤ x j)
    (lam : ι → ℝ)
    (hlam_max : ∀ j ∈ J, IsGreatest {t : ℝ | xbar + t • extremeRay I abar j ∈ S} (lam j)) :
    (∑ j ∈ J, (lam j)⁻¹ * xbar j) < 1 ∧ ∀ x ∈ PI, 1 ≤ ∑ j ∈ J, (lam j)⁻¹ * x j := by
  obtain ⟨hconv, hint, hempty⟩ := hPIFree
  have hlpos : ∀ j ∈ J, 0 < lam j := fun j hj => DK88.lam_pos S xbar _ hint _ (hlam_max j hj)
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_zero (fun j hj => by rw [hxbarJ j hj, mul_zero])]; norm_num
  intro x hxP
  obtain ⟨hI, hJ⟩ := hPI_cone x hxP
  by_contra hlt
  push Not at hlt
  set s := ∑ j ∈ J, (lam j)⁻¹ * x j with hs
  have hw : ∀ j ∈ J, 0 ≤ (lam j)⁻¹ * x j := fun j hj =>
    mul_nonneg (inv_nonneg.2 (hlpos j hj).le) (hJ j hj)
  have hs0 : 0 ≤ s := Finset.sum_nonneg hw
  -- decomposition x = xbar + Σ x_j r^j
  have hdec : x = xbar + ∑ j ∈ J, x j • extremeRay I abar j := by
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, extremeRay]
    rcases hcover i with hi | hi
    · have hiJ : i ∉ J := Finset.disjoint_left.1 hIJ hi
      rw [hI i hi]
      have : ∀ j ∈ J, x j * (if i = j then (1:ℝ) else if i ∈ I then -abar i j else 0)
          = -(abar i j * x j) := by
        intro j hj
        have : i ≠ j := fun e => hiJ (e ▸ hj)
        rw [if_neg this, if_pos hi]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]; ring
    · rw [hxbarJ i hi, zero_add]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; rw [if_neg (Ne.symm hne)]
        have : i ∉ I := fun h => Finset.disjoint_left.1 hIJ h hi
        rw [if_neg this, mul_zero]
      · intro h; exact absurd hi h
  have hpS : ∀ j ∈ J, xbar + lam j • extremeRay I abar j ∈ S := fun j hj => (hlam_max j hj).1
  have hxint : x ∈ interior S := by
    rcases hs0.lt_or_eq with hpos | hzero
    · -- y := Σ (w_j / s) p_j ∈ S
      set y := ∑ j ∈ J, (((lam j)⁻¹ * x j) / s) • (xbar + lam j • extremeRay I abar j) with hy
      have hyS : y ∈ S := by
        apply hconv.sum_mem
        · intro j hj; exact div_nonneg (hw j hj) hpos.le
        · rw [← Finset.sum_div, ← hs, div_self hpos.ne']
        · exact hpS
      have hmem := hconv.combo_interior_self_mem_interior hint hyS (a := 1 - s) (b := s)
        (by linarith) hpos.le (by ring)
      convert hmem using 1
      rw [hy, Finset.smul_sum]; conv_lhs => rw [hdec]
      simp only [smul_add, smul_smul]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul]
      have e1 : ∑ j ∈ J, s * ((lam j)⁻¹ * x j / s) = s := by
        rw [← Finset.mul_sum, ← Finset.sum_div, ← hs, mul_div_cancel₀ _ hpos.ne']
      have e2 : ∀ j ∈ J, (s * ((lam j)⁻¹ * x j / s * lam j)) • extremeRay I abar j =
          x j • extremeRay I abar j := by
        intro j hj
        congr 1
        field_simp [hpos.ne', (hlpos j hj).ne']
      rw [e1, Finset.sum_congr rfl e2, sub_smul, one_smul]
      abel
    · have hx0 : ∀ j ∈ J, x j = 0 := by
        intro j hj
        have := (Finset.sum_eq_zero_iff_of_nonneg hw).1 hzero.symm j hj
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (inv_ne_zero (hlpos j hj).ne')
        · exact h
      rw [hdec, Finset.sum_eq_zero (fun j hj => by rw [hx0 j hj, zero_smul]), add_zero]
      exact hint
  have : x ∈ interior S ∩ PI := ⟨hxint, hxP⟩
  rw [hempty] at this
  exact this
