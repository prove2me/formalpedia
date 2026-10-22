-- Prove2me | solution 1 for FairRandomObject.Bads.proposition_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:54:49.408985+00:00
-- url     : https://prove2.me/submissions/c351e941-92ef-4d26-88e2-a0e209e752e9

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy
import Theorems.Thm_FairRandomObject_Bads_prop_14_delta

open FairRandomObject.Bads

theorem solution {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hsym : IsSymmetric ϕ) :
    FairShareBad ϕ ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ Satisfies9 ϕ θ := by
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnpos : (0:ℝ) < n := by linarith
  have hle1 : ∀ x : Fin n → ℝ, 0 ≤ x → ∀ i, ϕ x i ≤ 1 := by
    intro x hx i
    have hs := hϕ.2 x hx
    rw [← hs.2]
    exact Finset.single_le_sum (fun j _ => hs.1 j) (Finset.mem_univ i)
  constructor
  · intro hfs
    obtain ⟨δ, hδ0, hδ⟩ := prop_14_delta hn ϕ hϕ hsym hfs
    have hδ1 : δ * ((n:ℝ) - 1) ≤ 1 := by
      set i0 : Fin n := ⟨0, by omega⟩
      set e : Fin n → ℝ := fun j => if j = i0 then 1 else 0 with he
      have he0 : 0 ≤ e := fun j => by simp only [e]; split_ifs <;> norm_num
      have hei : 0 < e i0 := by simp [e]
      have h := hδ e he0 i0 hei
      have hm : mean e = 1 / n := by
        unfold mean; simp [e]
      have hϕ0 : 0 ≤ ϕ e i0 := (hϕ.2 e he0).1 i0
      rw [hm] at h
      simp only [e, if_pos rfl, div_one] at h
      have : 0 ≤ 1 / (n:ℝ) + δ * (1 / n - 1) := le_trans hϕ0 h
      have := mul_nonneg hnpos.le this
      have e1 : (n:ℝ) * (1 / n + δ * (1 / n - 1)) = 1 + δ * (1 - n) := by field_simp
      nlinarith
    refine ⟨δ * ((n:ℝ) - 1), mul_nonneg hδ0 hn1.le, hδ1, ?_⟩
    intro x hx i
    unfold bound9
    split_ifs with h0
    · exact hle1 x hx i
    · have hxi : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm h0)
      have hc : δ * ((n:ℝ) - 1) / ((n:ℝ) - 1) = δ := by field_simp
      rw [hc]
      exact le_min (hδ x hx i hxi) (hle1 x hx i)
  · rintro ⟨θ, hθ0, hθ1, h9⟩ μ hμ i
    obtain ⟨hprob, hnull, hint⟩ := hμ
    have hae : ∀ᵐ x ∂μ, 0 ≤ x := MeasureTheory.ae_iff.mpr hnull
    set L : (Fin n → ℝ) → ℝ := fun x => x i / n + θ / ((n:ℝ) - 1) * (mean x - x i) with hL
    have hbound : ∀ x : Fin n → ℝ, 0 ≤ x → 0 ≤ ϕ x i * x i ∧ ϕ x i * x i ≤ L x := by
      intro x hx
      have h0 : 0 ≤ ϕ x i * x i := mul_nonneg ((hϕ.2 x hx).1 i) (hx i)
      refine ⟨h0, ?_⟩
      have hmean : 0 ≤ mean x := by
        unfold mean; exact div_nonneg (Finset.sum_nonneg (fun j _ => hx j)) hnpos.le
      by_cases hxi : x i = 0
      · simp only [L, hxi, mul_zero, zero_div, zero_add, sub_zero]
        positivity
      · have hxp : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hxi)
        have h1 := h9 x hx i
        unfold bound9 at h1
        rw [if_neg hxi] at h1
        have h2 : ϕ x i ≤ 1 / n + θ / ((n:ℝ) - 1) * (mean x / x i - 1) :=
          le_trans h1 (min_le_left _ _)
        have h3 := mul_le_mul_of_nonneg_right h2 hxp.le
        have h4 : (1 / n + θ / ((n:ℝ) - 1) * (mean x / x i - 1)) * x i = L x := by
          simp only [L]; field_simp
        linarith
    have hmeanint : MeasureTheory.Integrable (fun x : Fin n → ℝ => mean x) μ := by
      unfold mean
      exact (MeasureTheory.integrable_finsetSum _ (fun j _ => (hint j).1)).div_const _
    have hgi : MeasureTheory.Integrable L μ := by
      simp only [L]
      exact ((hint i).1.div_const _).add ((hmeanint.sub (hint i).1).const_mul _)
    have hle := MeasureTheory.integral_mono_of_nonneg
      (f := fun x => ϕ x i * x i) (by filter_upwards [hae] with x hx using
        (hbound x hx).1) hgi (by filter_upwards [hae] with x hx using (hbound x hx).2)
    refine le_trans hle (le_of_eq ?_)
    have hm1 : ∫ x, mean x ∂μ = 1 := by
      unfold mean
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_finsetSum _ (fun j _ => (hint j).1)]
      simp only [fun j => (hint j).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      field_simp
    have hA : MeasureTheory.Integrable (fun x : Fin n → ℝ => x i / n) μ := (hint i).1.div_const _
    have hD : MeasureTheory.Integrable (fun x : Fin n → ℝ => mean x - x i) μ :=
      hmeanint.sub (hint i).1
    have hB : MeasureTheory.Integrable
        (fun x : Fin n → ℝ => θ / ((n:ℝ) - 1) * (mean x - x i)) μ := hD.const_mul _
    simp only [L]
    rw [MeasureTheory.integral_add hA hB, MeasureTheory.integral_div,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hmeanint (hint i).1,
      hm1, (hint i).2]
    ring
