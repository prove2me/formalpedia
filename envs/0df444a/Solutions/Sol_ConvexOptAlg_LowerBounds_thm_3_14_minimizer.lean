-- Prove2me | solution 1 for ConvexOptAlg.LowerBounds.thm_3_14_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:59:03.813415+00:00
-- url     : https://prove2.me/submissions/00bb6cb8-4e3b-47c5-b7f1-f2d0101c4dea

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs
set_option autoImplicit false

open scoped InnerProductSpace
open ConvexOptAlg.LowerBounds

private lemma mem_span_basisVec_Icc_iff {n : ℕ} (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k) ↔
      ∀ j : Fin n, k ≤ (j : ℕ) → y j = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    { carrier := {y | ∀ j : Fin n, k ≤ (j : ℕ) → y j = 0}
      add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
      zero_mem' := fun j _ => rfl
      smul_mem' := fun c a ha j hj => by simp [ha j hj] }
  constructor
  · intro hy
    have h_le : Submodule.span ℝ (basisVec n '' Set.Icc 1 k) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨i, ⟨hi1, hik⟩, rfl⟩ j hj
      simp only [basisVec, WithLp.ofLp_toLp, if_neg (by omega : ¬(j : ℕ) + 1 = i)]
    exact h_le hy
  · intro hy
    have hy_sum : y = ∑ j : Fin n, (y j) • basisVec n ((j : ℕ) + 1) := by
      ext l
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      have : (∑ j : Fin n, ((y j) • basisVec n ((j : ℕ) + 1)).ofLp l) =
          ∑ j : Fin n, if j = l then y j else 0 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        change y j * (if (l : ℕ) + 1 = (j : ℕ) + 1 then (1 : ℝ) else 0) =
          if j = l then y j else 0
        by_cases hjl : j = l
        · subst hjl; simp
        · have hne : ¬(l : ℕ) + 1 = (j : ℕ) + 1 := by
            intro h
            apply hjl
            ext
            omega
          rw [if_neg hne, if_neg hjl, mul_zero]
      rw [this, Finset.sum_ite_eq', if_pos (Finset.mem_univ l)]
    rw [hy_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : k ≤ (j : ℕ)
    · rw [hy j hj, zero_smul]
      exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact ⟨(j : ℕ) + 1, ⟨by omega, by omega⟩, rfl⟩

private lemma tridiag_symm (n k : ℕ) (a b : Fin n) :
    (tridiag n k) a b = (tridiag n k) b a := by
  dsimp [tridiag]
  have h1 : ((a : ℕ) = (b : ℕ) ∧ (a : ℕ) < k) ↔ ((b : ℕ) = (a : ℕ) ∧ (b : ℕ) < k) := by omega
  have h2 : (((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧ (a : ℕ) < k ∧ (b : ℕ) ≠ k) ↔
      (((a : ℕ) + 1 = (b : ℕ) ∨ (a : ℕ) = (b : ℕ) + 1) ∧ (b : ℕ) < k ∧ (a : ℕ) ≠ k) := by omega
  by_cases hc1 : (b : ℕ) = (a : ℕ) ∧ (b : ℕ) < k
  · rw [if_pos (h1.mpr hc1), if_pos hc1]
  · rw [if_neg (mt h1.mp hc1), if_neg hc1]
    by_cases hc2 : ((a : ℕ) + 1 = (b : ℕ) ∨ (a : ℕ) = (b : ℕ) + 1) ∧ (b : ℕ) < k ∧ (a : ℕ) ≠ k
    · rw [if_pos (h2.mpr hc2), if_pos hc2]
    · rw [if_neg (mt h2.mp hc2), if_neg hc2]

private lemma tridiag_mulVec_ge {n k : ℕ} (y : EuclideanSpace ℝ (Fin n)) (a : Fin n)
    (ha : k ≤ (a : ℕ)) :
    ((tridiag n k).mulVec y.ofLp) a = 0 := by
  dsimp [Matrix.mulVec, dotProduct, tridiag]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [if_neg (by omega), if_neg (by omega), zero_mul]

private lemma tridiag_mulVec_lt {n k : ℕ} (hkn : k ≤ n) (y : EuclideanSpace ℝ (Fin n))
    (a : Fin n) (ha : (a : ℕ) < k) :
    ((tridiag n k).mulVec y.ofLp) a =
      2 * y.ofLp a -
        (if h1 : 0 < (a : ℕ) then y.ofLp ⟨(a : ℕ) - 1, by omega⟩ else 0) -
        (if h2 : (a : ℕ) + 1 < k then y.ofLp ⟨(a : ℕ) + 1, by omega⟩ else 0) := by
  dsimp [Matrix.mulVec, dotProduct]
  have h_term : ∀ b : Fin n, (tridiag n k) a b * y.ofLp b =
      (if b = a then 2 * y.ofLp a else 0) -
      (if h1 : 0 < (a : ℕ) then
        if b = ⟨(a : ℕ) - 1, by omega⟩ then y.ofLp ⟨(a : ℕ) - 1, by omega⟩ else 0 else 0) -
      (if h2 : (a : ℕ) + 1 < k then
        if b = ⟨(a : ℕ) + 1, by omega⟩ then y.ofLp ⟨(a : ℕ) + 1, by omega⟩ else 0 else 0) := by
    intro b
    dsimp [tridiag]
    by_cases hba : b = a
    · subst hba
      rw [if_pos ⟨rfl, ha⟩, if_pos rfl]
      have h_t1 : (if h1 : 0 < (b : ℕ) then
          if b = ⟨(b : ℕ) - 1, by omega⟩ then y.ofLp ⟨(b : ℕ) - 1, by omega⟩ else 0 else 0) = 0 := by
        split_ifs with h1 h_eq1
        · have := congr_arg Fin.val h_eq1
          dsimp at this
          omega
        · rfl
        · rfl
      have h_t2 : (if h2 : (b : ℕ) + 1 < k then
          if b = ⟨(b : ℕ) + 1, by omega⟩ then y.ofLp ⟨(b : ℕ) + 1, by omega⟩ else 0 else 0) = 0 := by
        split_ifs with h2 h_eq2
        · have := congr_arg Fin.val h_eq2
          dsimp at this
          omega
        · rfl
        · rfl
      rw [h_t1, h_t2]
      ring
    · have hba_val : (a : ℕ) ≠ (b : ℕ) := fun h => hba (Fin.ext h.symm)
      rw [if_neg (by omega), if_neg hba]
      by_cases h_prev : 0 < (a : ℕ) ∧ (b : ℕ) + 1 = (a : ℕ)
      · have h_adj : ((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧ (a : ℕ) < k ∧ (b : ℕ) ≠ k :=
          ⟨Or.inl h_prev.2, ha, by omega⟩
        rw [if_pos h_adj, dif_pos h_prev.1]
        have hb_eq1 : b = ⟨(a : ℕ) - 1, by omega⟩ := by ext; dsimp; omega
        rw [if_pos hb_eq1, ← hb_eq1]
        have h_t2 : (if h2 : (a : ℕ) + 1 < k then
            if b = ⟨(a : ℕ) + 1, by omega⟩ then y.ofLp ⟨(a : ℕ) + 1, by omega⟩ else 0 else 0) = 0 := by
          split_ifs with h2 h_eq2
          · have := congr_arg Fin.val h_eq2
            dsimp at this
            omega
          · rfl
          · rfl
        rw [h_t2]
        ring
      · by_cases h_next : (a : ℕ) + 1 < k ∧ (b : ℕ) = (a : ℕ) + 1
        · have h_adj : ((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧ (a : ℕ) < k ∧ (b : ℕ) ≠ k :=
            ⟨Or.inr h_next.2, ha, by omega⟩
          rw [if_pos h_adj, dif_pos h_next.1]
          have hb_eq2 : b = ⟨(a : ℕ) + 1, by omega⟩ := by ext; dsimp; omega
          rw [if_pos hb_eq2, ← hb_eq2]
          have h_t1 : (if h1 : 0 < (a : ℕ) then
              if b = ⟨(a : ℕ) - 1, by omega⟩ then y.ofLp ⟨(a : ℕ) - 1, by omega⟩ else 0 else 0) = 0 := by
            split_ifs with h1 h_eq1
            · have := congr_arg Fin.val h_eq1
              dsimp at this
              omega
            · rfl
            · rfl
          rw [h_t1]
          ring
        · have h_not_adj : ¬(((b : ℕ) + 1 = (a : ℕ) ∨ (b : ℕ) = (a : ℕ) + 1) ∧
              (a : ℕ) < k ∧ (b : ℕ) ≠ k) := by omega
          rw [if_neg h_not_adj]
          have h_t1 : (if h1 : 0 < (a : ℕ) then
              if b = ⟨(a : ℕ) - 1, by omega⟩ then y.ofLp ⟨(a : ℕ) - 1, by omega⟩ else 0 else 0) = 0 := by
            split_ifs with h1 h_eq1
            · have := congr_arg Fin.val h_eq1
              dsimp at this
              omega
            · rfl
            · rfl
          have h_t2 : (if h2 : (a : ℕ) + 1 < k then
              if b = ⟨(a : ℕ) + 1, by omega⟩ then y.ofLp ⟨(a : ℕ) + 1, by omega⟩ else 0 else 0) = 0 := by
            split_ifs with h2 h_eq2
            · have := congr_arg Fin.val h_eq2
              dsimp at this
              omega
            · rfl
            · rfl
          rw [h_t1, h_t2]
          ring
  simp_rw [h_term]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]
  congr 1
  · congr 1
    split_ifs with h1
    · rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    · exact Finset.sum_const_zero
  · split_ifs with h2
    · rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    · exact Finset.sum_const_zero

private lemma quadForm_tridiag_nonneg_and_eq_zero {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (d : EuclideanSpace ℝ (Fin n)) :
    0 ≤ quadForm (tridiag n k) d ∧
      (quadForm (tridiag n k) d = 0 → ∀ a : Fin n, (a : ℕ) < k → d.ofLp a = 0) := by
  let v : ℕ → ℝ := fun i => if h : i < k then d.ofLp ⟨i, by omega⟩ else 0
  let ψ : ℕ → ℝ := fun i => if i = 0 then 0 else (v i) ^ 2 - v (i - 1) * v i
  have h_row_prod : ∀ a : Fin n,
      d.ofLp a * ((tridiag n k).mulVec d.ofLp) a =
        v (a : ℕ) * (2 * v (a : ℕ) - (if 0 < (a : ℕ) then v ((a : ℕ) - 1) else 0) -
          v ((a : ℕ) + 1)) := by
    intro a
    by_cases ha : (a : ℕ) < k
    · rw [tridiag_mulVec_lt hkn d a ha]
      have hva : v (a : ℕ) = d.ofLp a := dif_pos ha
      have hv_prev : (if 0 < (a : ℕ) then v ((a : ℕ) - 1) else 0) =
          (if h1 : 0 < (a : ℕ) then d.ofLp ⟨(a : ℕ) - 1, by omega⟩ else 0) := by
        split_ifs with h1
        · exact dif_pos (by omega)
        · rfl
      have hv_next : v ((a : ℕ) + 1) =
          (if h2 : (a : ℕ) + 1 < k then d.ofLp ⟨(a : ℕ) + 1, by omega⟩ else 0) := by
        dsimp [v]
      rw [hva, hv_prev, hv_next]
    · rw [tridiag_mulVec_ge d a (by omega), mul_zero]
      have hva : v (a : ℕ) = 0 := dif_neg ha
      rw [hva, zero_mul]
  have h_sum_range : quadForm (tridiag n k) d =
      ∑ i ∈ Finset.range n,
        v i * (2 * v i - (if 0 < i then v (i - 1) else 0) - v (i + 1)) := by
    dsimp [quadForm, dotProduct]
    simp_rw [h_row_prod]
    rw [← Fin.sum_univ_eq_sum_range]
  have h_term_id : ∀ i : ℕ,
      v i * (2 * v i - (if 0 < i then v (i - 1) else 0) - v (i + 1)) =
        ((if i = 0 then (v 0) ^ 2 else 0) + (v i - v (i + 1)) ^ 2) + (ψ i - ψ (i + 1)) := by
    intro i
    rcases i with _ | i
    · dsimp [ψ]
      ring
    · dsimp [ψ]
      ring
  have h_tel : ∀ m : ℕ, ∑ i ∈ Finset.range m, (ψ i - ψ (i + 1)) = ψ 0 - ψ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hψ0 : ψ 0 = 0 := rfl
  have hψn : ψ n = 0 := by
    dsimp [ψ]
    split_ifs with hn0
    · rfl
    · have hvn : v n = 0 := dif_neg (by omega)
      rw [hvn]
      ring
  have h_quad_sq : quadForm (tridiag n k) d =
      ∑ i ∈ Finset.range n, ((if i = 0 then (v 0) ^ 2 else 0) + (v i - v (i + 1)) ^ 2) := by
    rw [h_sum_range]
    simp_rw [h_term_id]
    rw [Finset.sum_add_distrib, h_tel n, hψ0, hψn, sub_self, add_zero]
  have h_term_nonneg : ∀ i ∈ Finset.range n,
      0 ≤ (if i = 0 then (v 0) ^ 2 else 0) + (v i - v (i + 1)) ^ 2 := by
    intro i _
    split_ifs <;> positivity
  refine ⟨by rw [h_quad_sq]; exact Finset.sum_nonneg h_term_nonneg, ?_⟩
  intro h_zero
  rw [h_quad_sq] at h_zero
  have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg h_term_nonneg).mp h_zero
  have hv_zero : ∀ i : ℕ, i < k → v i = 0 := by
    intro i hi
    induction i with
    | zero =>
      have h0 := h_all_zero 0 (Finset.mem_range.mpr (by omega))
      rw [if_pos rfl] at h0
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 0 - v 1)]
    | succ i ih =>
      have hi_prev : v i = 0 := ih (by omega)
      have hi_mem := h_all_zero i (Finset.mem_range.mpr (by omega))
      have h_nonneg1 : 0 ≤ (if i = 0 then (v 0) ^ 2 else 0) := by split_ifs <;> positivity
      have h_sq_zero : (v i - v (i + 1)) ^ 2 = 0 := by
        nlinarith [sq_nonneg (v i - v (i + 1))]
      have h_sub_zero : v i - v (i + 1) = 0 := sq_eq_zero_iff.mp h_sq_zero
      linarith
  intro a ha
  exact (dif_pos ha).symm.trans (hv_zero (a : ℕ) ha)

theorem solution (n k : ℕ) (β : ℝ) (hβ : 0 < β) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (tridiag n k).mulVec (xstarK n k).ofLp = (basisVec n 1).ofLp ∧
      xstarK n k ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k) ∧
      (∀ y ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k),
        (tridiag n k).mulVec y.ofLp = (basisVec n 1).ofLp → y = xstarK n k) ∧
      (∀ y, fK n β k (xstarK n k) ≤ fK n β k y) ∧
      ⨅ y, fK n β k y = fK n β k (xstarK n k) ∧
      fK n β k (xstarK n k) = -(β / 8) * ⟪xstarK n k, basisVec n 1⟫_ℝ ∧
      fK n β k (xstarK n k) = -(β / 8) * (1 - 1 / ((k : ℝ) + 1)) := by
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := hk1_pos.ne'
  have hxstar_lt : ∀ c : Fin n, (c : ℕ) < k →
      (xstarK n k).ofLp c = 1 - ((c : ℕ) + 1 : ℝ) / ((k : ℝ) + 1) := by
    intro c hc
    dsimp [xstarK]
    exact if_pos (by omega)
  have h_sol : (tridiag n k).mulVec (xstarK n k).ofLp = (basisVec n 1).ofLp := by
    ext a
    by_cases ha : (a : ℕ) < k
    · rw [tridiag_mulVec_lt hkn (xstarK n k) a ha, hxstar_lt a ha]
      dsimp [basisVec]
      by_cases ha0 : (a : ℕ) = 0
      · have ha1 : ¬0 < (a : ℕ) := by omega
        have he1 : (a : ℕ) + 1 = 1 := by omega
        have ha_real : ((a : ℕ) : ℝ) = 0 := by exact_mod_cast ha0
        rw [dif_neg ha1, if_pos he1]
        split_ifs with h2
        · rw [hxstar_lt ⟨(a : ℕ) + 1, by omega⟩ h2]
          dsimp
          push_cast
          rw [ha_real]
          field_simp
          ring
        · have hk_eq1 : k = 1 := by omega
          rw [ha_real, hk_eq1]
          push_cast
          norm_num
      · have ha1 : 0 < (a : ℕ) := by omega
        have he1 : ¬(a : ℕ) + 1 = 1 := by omega
        rw [dif_pos ha1, if_neg he1, hxstar_lt ⟨(a : ℕ) - 1, by omega⟩ (by dsimp; omega)]
        dsimp
        have h_cast_sub : (((a : ℕ) - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
          rw [Nat.cast_sub ha1, Nat.cast_one]
        rw [h_cast_sub]
        split_ifs with h2
        · rw [hxstar_lt ⟨(a : ℕ) + 1, by omega⟩ h2]
          dsimp
          push_cast
          field_simp
          ring
        · have ha_eq : (a : ℕ) + 1 = k := by omega
          have ha_real : (a : ℝ) + 1 = (k : ℝ) := by exact_mod_cast ha_eq
          field_simp
          linarith
    · rw [tridiag_mulVec_ge (xstarK n k) a (by omega)]
      dsimp [basisVec]
      rw [if_neg (by omega)]
  have h_mem_span : xstarK n k ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k) := by
    rw [mem_span_basisVec_Icc_iff]
    intro j hj
    dsimp [xstarK]
    exact if_neg (by omega)
  have h_uniq : ∀ y ∈ Submodule.span ℝ (basisVec n '' Set.Icc 1 k),
      (tridiag n k).mulVec y.ofLp = (basisVec n 1).ofLp → y = xstarK n k := by
    intro y hy hy_sol
    let d := y - xstarK n k
    have hd_mul : (tridiag n k).mulVec d.ofLp = 0 := by
      have h_ofLp : d.ofLp = y.ofLp - (xstarK n k).ofLp := rfl
      rw [h_ofLp, Matrix.mulVec_sub, hy_sol, h_sol, sub_self]
    have hd_quad : quadForm (tridiag n k) d = 0 := by
      dsimp [quadForm]
      rw [hd_mul, dotProduct_zero]
    have hd_lt := (quadForm_tridiag_nonneg_and_eq_zero hk hkn d).2 hd_quad
    have hy_ge := (mem_span_basisVec_Icc_iff k y).mp hy
    have hx_ge := (mem_span_basisVec_Icc_iff k (xstarK n k)).mp h_mem_span
    ext a
    by_cases ha : (a : ℕ) < k
    · have h0 := hd_lt a ha
      change y.ofLp a - (xstarK n k).ofLp a = 0 at h0
      linarith
    · rw [hy_ge a (by omega), hx_ge a (by omega)]
  have h_fK_diff : ∀ y : EuclideanSpace ℝ (Fin n),
      fK n β k y = fK n β k (xstarK n k) + β / 8 * quadForm (tridiag n k) (y - xstarK n k) := by
    intro y
    let d := y - xstarK n k
    have hy_eq : y = xstarK n k + d := (add_sub_cancel (xstarK n k) y).symm
    have h_symm : dotProduct (xstarK n k).ofLp ((tridiag n k).mulVec d.ofLp) =
        dotProduct d.ofLp ((tridiag n k).mulVec (xstarK n k).ofLp) := by
      dsimp [dotProduct, Matrix.mulVec]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      rw [tridiag_symm n k a b]
      ring
    have h_quad_add : quadForm (tridiag n k) (xstarK n k + d) =
        quadForm (tridiag n k) (xstarK n k) + 2 * ⟪d, basisVec n 1⟫_ℝ +
          quadForm (tridiag n k) d := by
      dsimp [quadForm]
      rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
        h_symm, h_sol, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct_comm (basisVec n 1).ofLp d.ofLp]
      ring
    change fK n β k y = fK n β k (xstarK n k) + β / 8 * quadForm (tridiag n k) d
    rw [hy_eq]
    dsimp [fK]
    rw [h_quad_add, inner_add_left]
    ring
  have h_min : ∀ y, fK n β k (xstarK n k) ≤ fK n β k y := by
    intro y
    rw [h_fK_diff y]
    have h_nonneg := (quadForm_tridiag_nonneg_and_eq_zero hk hkn (y - xstarK n k)).1
    have : 0 ≤ β / 8 * quadForm (tridiag n k) (y - xstarK n k) := by positivity
    linarith
  have h_inf : (⨅ y, fK n β k y) = fK n β k (xstarK n k) := by
    have h_bdd : BddBelow (Set.range (fK n β k)) := ⟨fK n β k (xstarK n k), by
      rintro _ ⟨y, rfl⟩
      exact h_min y⟩
    exact le_antisymm (ciInf_le h_bdd (xstarK n k)) (le_ciInf h_min)
  have h_val1 : fK n β k (xstarK n k) = -(β / 8) * ⟪xstarK n k, basisVec n 1⟫_ℝ := by
    dsimp [fK, quadForm]
    rw [h_sol, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm (basisVec n 1).ofLp (xstarK n k).ofLp]
    ring
  have h_inner_e1 : ⟪xstarK n k, basisVec n 1⟫_ℝ = 1 - 1 / ((k : ℝ) + 1) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    dsimp [dotProduct, basisVec]
    have h_term : ∀ j : Fin n, (if (j : ℕ) + 1 = 1 then (1 : ℝ) else 0) * (xstarK n k).ofLp j =
        if j = ⟨0, by omega⟩ then (xstarK n k).ofLp ⟨0, by omega⟩ else 0 := by
      intro j
      by_cases hj0 : j = ⟨0, by omega⟩
      · subst hj0
        simp
      · have hj1 : ¬(j : ℕ) + 1 = 1 := by
          intro h
          apply hj0
          ext
          dsimp
          omega
        rw [if_neg hj1, if_neg hj0, zero_mul]
    simp_rw [h_term]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
      hxstar_lt ⟨0, by omega⟩ (by dsimp; omega)]
    simp
  have h_val2 : fK n β k (xstarK n k) = -(β / 8) * (1 - 1 / ((k : ℝ) + 1)) := by
    rw [h_val1, h_inner_e1]
  exact ⟨h_sol, h_mem_span, h_uniq, h_min, h_inf, h_val1, h_val2⟩
