-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.sbf_iff_perturbed_level_sets_qdl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:09:33.027123+00:00
-- url     : https://prove2.me/submissions/dab2ec97-e613-4f43-9f1e-d2e016f10c66

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QDL
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LevelSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LinearWeightPlus

set_option autoImplicit false

namespace P6a9912a2

lemma lin_modular {V : Type*} [Fintype V] (x : V → ℝ) (p q : V → ℤ) :
    (∑ v, x v * (((p ⊔ q) v : ℤ) : ℝ)) + (∑ v, x v * (((p ⊓ q) v : ℤ) : ℝ)) =
    (∑ v, x v * ((p v : ℤ) : ℝ)) + (∑ v, x v * ((q v : ℤ) : ℝ)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.sup_apply, Pi.inf_apply]
  rcases le_total (p v) (q v) with h | h
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; try ring
  · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]; try ring

lemma two_lt {α : ℝ} {y z : WithTop ℝ} (hy : (α : WithTop ℝ) < y)
    (hz : (α : WithTop ℝ) < z) : ((α + α : ℝ) : WithTop ℝ) < y + z := by
  induction y using WithTop.recTopCoe with
  | top => simp
  | coe c =>
    induction z using WithTop.recTopCoe with
    | top => simp
    | coe d =>
      rw [WithTop.coe_lt_coe] at hy hz
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]; linarith

lemma approx {r : ℝ} {y z : WithTop ℝ} (h : (r : WithTop ℝ) < y + z) :
    ∃ c d : ℝ, (c : WithTop ℝ) ≤ y ∧ (d : WithTop ℝ) ≤ z ∧ r < c + d := by
  induction y using WithTop.recTopCoe with
  | top =>
    induction z using WithTop.recTopCoe with
    | top => exact ⟨r + 1, 0, le_top, le_top, by linarith⟩
    | coe d => exact ⟨r - d + 1, d, le_top, le_rfl, by linarith⟩
  | coe c =>
    induction z using WithTop.recTopCoe with
    | top => exact ⟨c, r - c + 1, le_rfl, le_top, by linarith⟩
    | coe d =>
      rw [← WithTop.coe_add, WithTop.coe_lt_coe] at h
      exact ⟨c, d, le_rfl, le_rfl, h⟩

open DiscreteConvex.LConvexFunctionsD in
theorem fwd {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ)
    (h : SBF g) : ∀ x : V → ℝ, ∀ alpha : ℝ, QDL (LevelSet (LinearWeightPlus g x) alpha) := by
  intro x alpha p hp q hq
  simp only [LevelSet, Set.mem_ofPred_eq, LinearWeightPlus] at hp hq ⊢
  set fp := ∑ v, x v * ((p v : ℤ) : ℝ) with hfp
  set fq := ∑ v, x v * ((q v : ℤ) : ℝ) with hfq
  set fm := ∑ v, x v * (((p ⊓ q) v : ℤ) : ℝ) with hfm
  set fJ := ∑ v, x v * (((p ⊔ q) v : ℤ) : ℝ) with hfJ
  have hlin : fJ + fm = fp + fq := lin_modular x p q
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  have h1 := two_lt hc.1 hc.2
  have hs := h p q
  have h2 : (g (p ⊓ q) + (fm : WithTop ℝ)) + (g (p ⊔ q) + (fJ : WithTop ℝ)) ≤
      (g p + (fp : WithTop ℝ)) + (g q + (fq : WithTop ℝ)) := by
    calc (g (p ⊓ q) + (fm : WithTop ℝ)) + (g (p ⊔ q) + (fJ : WithTop ℝ))
        = (g (p ⊔ q) + g (p ⊓ q)) + ((fJ + fm : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_add]; abel
      _ ≤ (g p + g q) + ((fp + fq : ℝ) : WithTop ℝ) := by
          rw [hlin]; exact add_le_add hs le_rfl
      _ = (g p + (fp : WithTop ℝ)) + (g q + (fq : WithTop ℝ)) := by
          rw [WithTop.coe_add]; abel
  have h3 : (g p + (fp : WithTop ℝ)) + (g q + (fq : WithTop ℝ)) ≤
      ((alpha + alpha : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_add]; exact add_le_add hp hq
  exact lt_irrefl _ (h1.trans_le (h2.trans h3))

lemma pt_p (t u : ℝ) (a b : ℤ) :
    (if b < a then t else if a < b then u else 0) * ((a : ℤ) : ℝ) =
      (if b < a then t else if a < b then u else 0) * (((min a b : ℤ)) : ℝ)
        + t * (((a : ℤ) : ℝ) - ((min a b : ℤ) : ℝ)) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [if_neg (not_lt.mpr hab.le), if_pos hab, min_eq_left hab.le]; ring
  · subst hab; simp
  · rw [if_pos hab, min_eq_right hab.le]; ring

lemma pt_q (t u : ℝ) (a b : ℤ) :
    (if b < a then t else if a < b then u else 0) * ((b : ℤ) : ℝ) =
      (if b < a then t else if a < b then u else 0) * (((min a b : ℤ)) : ℝ)
        + u * (((b : ℤ) : ℝ) - ((min a b : ℤ) : ℝ)) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [if_neg (not_lt.mpr hab.le), if_pos hab, min_eq_left hab.le]; ring
  · subst hab; simp
  · rw [if_pos hab, min_eq_right hab.le]; ring

lemma pt_J (t u : ℝ) (a b : ℤ) :
    (if b < a then t else if a < b then u else 0) * (((max a b : ℤ)) : ℝ) =
      (if b < a then t else if a < b then u else 0) * (((min a b : ℤ)) : ℝ)
        + t * (((a : ℤ) : ℝ) - ((min a b : ℤ) : ℝ))
        + u * (((b : ℤ) : ℝ) - ((min a b : ℤ) : ℝ)) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [if_neg (not_lt.mpr hab.le), if_pos hab, min_eq_left hab.le, max_eq_right hab.le]; ring
  · subst hab; simp
  · rw [if_pos hab, min_eq_right hab.le, max_eq_left hab.le]; ring

open DiscreteConvex.LConvexFunctionsD in
theorem bwd {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ)
    (h : ∀ x : V → ℝ, ∀ alpha : ℝ, QDL (LevelSet (LinearWeightPlus g x) alpha)) :
    SBF g := by
  intro p q
  by_cases hA : ∃ v, q v < p v
  swap
  · push Not at hA
    have hpq : p ≤ q := fun v => hA v
    rw [sup_eq_right.mpr hpq, inf_eq_left.mpr hpq]
    exact le_of_eq (add_comm _ _)
  by_cases hB : ∃ v, p v < q v
  swap
  · push Not at hB
    have hqp : q ≤ p := fun v => hB v
    rw [sup_eq_left.mpr hqp, inf_eq_right.mpr hqp]
  rcases eq_or_ne (g p) ⊤ with hpt | hpt
  · rw [hpt, top_add]; exact le_top
  rcases eq_or_ne (g q) ⊤ with hqt | hqt
  · rw [hqt, add_top]; exact le_top
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hpt
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hqt
  rw [ge_iff_le, ← not_lt]
  intro hlt
  rw [← ha, ← hb, ← WithTop.coe_add] at hlt
  obtain ⟨d0, c0, hd0, hc0, hdc⟩ := approx hlt
  set D1 : ℝ := ∑ v, (((p v : ℤ) : ℝ) - ((min (p v) (q v) : ℤ) : ℝ)) with hD1
  set D2 : ℝ := ∑ v, (((q v : ℤ) : ℝ) - ((min (p v) (q v) : ℤ) : ℝ)) with hD2
  have hD1pos : 0 < D1 := by
    obtain ⟨w, hw⟩ := hA
    refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ _, ?_⟩
    · have : min (p v) (q v) ≤ p v := min_le_left _ _
      have : ((min (p v) (q v) : ℤ) : ℝ) ≤ ((p v : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    · rw [min_eq_right hw.le]
      have : ((q w : ℤ) : ℝ) < ((p w : ℤ) : ℝ) := by exact_mod_cast hw
      linarith
  have hD2pos : 0 < D2 := by
    obtain ⟨w, hw⟩ := hB
    refine Finset.sum_pos' (fun v _ => ?_) ⟨w, Finset.mem_univ _, ?_⟩
    · have : min (p v) (q v) ≤ q v := min_le_right _ _
      have : ((min (p v) (q v) : ℤ) : ℝ) ≤ ((q v : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    · rw [min_eq_left hw.le]
      have : ((p w : ℤ) : ℝ) < ((q w : ℤ) : ℝ) := by exact_mod_cast hw
      linarith
  set s : ℝ := (b - d0 + c0 - a) / 2 with hs
  set r : ℝ := a + s - b with hr
  set t : ℝ := s / D1 with ht
  set u : ℝ := r / D2 with hu
  have htD : t * D1 = s := div_mul_cancel₀ s hD1pos.ne'
  have huD : u * D2 = r := div_mul_cancel₀ r hD2pos.ne'
  set x : V → ℝ := fun v => if q v < p v then t else if p v < q v then u else 0 with hx
  set M : ℝ := ∑ v, x v * (((p ⊓ q) v : ℤ) : ℝ) with hM
  have fp : ∑ v, x v * ((p v : ℤ) : ℝ) = M + s := by
    rw [← htD, hD1, Finset.mul_sum, hM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hx, Pi.inf_apply]
    exact pt_p t u (p v) (q v)
  have fq : ∑ v, x v * ((q v : ℤ) : ℝ) = M + r := by
    rw [← huD, hD2, Finset.mul_sum, hM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hx, Pi.inf_apply]
    exact pt_q t u (p v) (q v)
  have fJ : ∑ v, x v * (((p ⊔ q) v : ℤ) : ℝ) = M + s + r := by
    rw [← htD, ← huD, hD1, hD2, Finset.mul_sum, Finset.mul_sum, hM,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [hx, Pi.inf_apply, Pi.sup_apply]
    exact pt_J t u (p v) (q v)
  have key := h x (a + s + M) p (by
      simp only [LevelSet, Set.mem_ofPred_eq, LinearWeightPlus]
      rw [fp, ← ha, ← WithTop.coe_add, WithTop.coe_le_coe]; linarith)
    q (by
      simp only [LevelSet, Set.mem_ofPred_eq, LinearWeightPlus]
      rw [fq, ← hb, ← WithTop.coe_add, WithTop.coe_le_coe]; linarith)
  simp only [LevelSet, Set.mem_ofPred_eq, LinearWeightPlus] at key
  rcases key with k | k
  · rw [← hM] at k
    have k2 : ((c0 + M : ℝ) : WithTop ℝ) ≤ ((a + s + M : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]; exact (add_le_add hc0 le_rfl).trans k
    rw [WithTop.coe_le_coe] at k2
    linarith
  · rw [fJ] at k
    have k2 : ((d0 + (M + s + r) : ℝ) : WithTop ℝ) ≤ ((a + s + M : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]; exact (add_le_add hd0 le_rfl).trans k
    rw [WithTop.coe_le_coe] at k2
    linarith

end P6a9912a2

open Classical in
open scoped Pointwise in
open DiscreteConvex.LConvexFunctionsD in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ) :
    SBF g ↔ ∀ x : V → ℝ, ∀ alpha : ℝ, QDL (LevelSet (LinearWeightPlus g x) alpha) := by
  exact ⟨P6a9912a2.fwd g, P6a9912a2.bwd g⟩
