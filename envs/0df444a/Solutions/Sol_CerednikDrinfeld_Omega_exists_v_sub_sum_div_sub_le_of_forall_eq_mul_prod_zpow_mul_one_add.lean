-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/062630cb-7d60-5397-aae5-529aefd3f97a

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add

set_option autoImplicit false

open CerednikDrinfeld.Omega

namespace LocCore

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

lemma v_natCast_le_one (n : ℕ) : Valued.v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

lemma v_intCast_le_one (m : ℤ) : Valued.v (m : K) ≤ 1 := by
  cases m with
  | ofNat n => simpa using v_natCast_le_one (K := K) n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast v_natCast_le_one (K := K) (n + 1)

lemma v_one_add_le_one {x : K} {s : Γ₀} (hs : s ≤ 1) (hx : Valued.v x ≤ s) :
    Valued.v (1 + x) ≤ 1 :=
  Valuation.map_add_le _ (by simp) (hx.trans hs)

lemma v_prod_one_add_le_one {ι : Type} (T : Finset ι) (x : ι → K) {s : Γ₀} (hs : s ≤ 1)
    (hx : ∀ i ∈ T, Valued.v (x i) ≤ s) : Valued.v (∏ i ∈ T, (1 + x i)) ≤ 1 := by
  rw [map_prod]
  exact Finset.prod_le_one' (fun i hi => v_one_add_le_one hs (hx i hi))

lemma v_prod_one_add_sub_one_le {ι : Type} [DecidableEq ι] (T : Finset ι) (x : ι → K) {s : Γ₀} (hs : s ≤ 1)
    (hx : ∀ i ∈ T, Valued.v (x i) ≤ s) : Valued.v (∏ i ∈ T, (1 + x i) - 1) ≤ s := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha]
    set P := ∏ i ∈ T, (1 + x i) with hP
    have hP1 : Valued.v (P - 1) ≤ s := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hy : Valued.v (x a) ≤ s := hx a (Finset.mem_insert_self a T)
    have : (1 + x a) * P - 1 = (P - 1) + ((P - 1) * x a + x a) := by ring
    rw [this]
    refine Valuation.map_add_le _ hP1 (Valuation.map_add_le _ ?_ hy)
    rw [map_mul]
    calc Valued.v (P - 1) * Valued.v (x a) ≤ s * 1 := mul_le_mul' hP1 (hy.trans hs)
      _ = s := mul_one s

lemma v_prodRem_le {ι : Type} [DecidableEq ι] (T : Finset ι) (x : ι → K) {s : Γ₀} (hs : s ≤ 1)
    (hx : ∀ i ∈ T, Valued.v (x i) ≤ s) :
    Valued.v (∏ i ∈ T, (1 + x i) - 1 - ∑ i ∈ T, x i) ≤ s * s := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    set P := ∏ i ∈ T, (1 + x i) with hP
    set S := ∑ i ∈ T, x i with hS
    have hx' : ∀ i ∈ T, Valued.v (x i) ≤ s := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have IH : Valued.v (P - 1 - S) ≤ s * s := ih hx'
    have hP1 : Valued.v (P - 1) ≤ s := v_prod_one_add_sub_one_le T x hs hx'
    have hy : Valued.v (x a) ≤ s := hx a (Finset.mem_insert_self a T)
    have : (1 + x a) * P - 1 - (x a + S) = (P - 1 - S) + (P - 1) * x a := by ring
    rw [this]
    refine Valuation.map_add_le _ IH ?_
    rw [map_mul]
    exact mul_le_mul' hP1 hy

lemma v_one_add_eq_one {u : K} (hu : Valued.v u < 1) : Valued.v (1 + u) = 1 := by
  simpa using Valuation.map_one_add_of_lt Valued.v hu

lemma v_one_add_pow_sub_le (u : K) (hu : Valued.v u ≤ 1) (n : ℕ) :
    Valued.v ((1 + u) ^ n - 1 - (n : K) * u) ≤ Valued.v u ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (1 + u) ^ (n + 1) - 1 - ((n + 1 : ℕ) : K) * u =
        ((1 + u) ^ n - 1 - (n : K) * u) * (1 + u) + (n : K) * (u * u) := by
      push_cast; ring
    rw [this]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [map_mul]
      calc Valued.v ((1 + u) ^ n - 1 - (n : K) * u) * Valued.v (1 + u) ≤ Valued.v u ^ 2 * 1 :=
            mul_le_mul' ih (v_one_add_le_one le_rfl hu)
        _ = Valued.v u ^ 2 := mul_one _
    · rw [map_mul, map_mul, pow_two]
      calc Valued.v (n : K) * (Valued.v u * Valued.v u) ≤ 1 * (Valued.v u * Valued.v u) :=
            mul_le_mul' (v_natCast_le_one n) le_rfl
        _ = Valued.v u * Valued.v u := one_mul _

lemma v_one_add_zpow_sub_le (u : K) (hu : Valued.v u < 1) (m : ℤ) :
    Valued.v ((1 + u) ^ m - 1 - (m : K) * u) ≤ Valued.v u ^ 2 := by
  have h1u : Valued.v (1 + u) = 1 := v_one_add_eq_one hu
  have h1u0 : (1 + u) ≠ 0 := fun h => by simp [h] at h1u
  cases m with
  | ofNat n => simpa using v_one_add_pow_sub_le u hu.le n
  | negSucc n =>

    set w : K := (1 + u)⁻¹ - 1 with hw
    have hwu : w = -u * (1 + u)⁻¹ := by
      rw [hw]; field_simp; ring
    have hvw : Valued.v w = Valued.v u := by
      rw [hwu, map_mul, Valuation.map_neg, map_inv₀, h1u, inv_one, mul_one]
    have hpow : (1 + u) ^ (Int.negSucc n) = (1 + w) ^ (n + 1) := by
      simp only [zpow_negSucc, hw, add_sub_cancel, inv_pow]
    have hcast : ((Int.negSucc n : ℤ) : K) = -((n + 1 : ℕ) : K) := by
      rw [Int.cast_negSucc] <;> try push_cast <;> try ring
    have key : (1 + u) ^ (Int.negSucc n) - 1 - ((Int.negSucc n : ℤ) : K) * u =
        ((1 + w) ^ (n + 1) - 1 - ((n + 1 : ℕ) : K) * w) + ((n + 1 : ℕ) : K) * (w + u) := by
      rw [hpow, hcast]; ring
    have hwu2 : w + u = u * u * (1 + u)⁻¹ := by
      rw [hw]; field_simp; ring
    rw [key]
    refine Valuation.map_add_le _ ?_ ?_
    · simpa [hvw] using v_one_add_pow_sub_le w (by rw [hvw]; exact hu.le) (n + 1)
    · rw [map_mul, hwu2, map_mul, map_mul, map_inv₀, h1u, inv_one, mul_one, pow_two]
      calc Valued.v ((n + 1 : ℕ) : K) * (Valued.v u * Valued.v u) ≤ 1 * (Valued.v u * Valued.v u) :=
            mul_le_mul' (v_natCast_le_one (n + 1)) le_rfl
        _ = Valued.v u * Valued.v u := one_mul _

end LocCore

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (f h : ↥(holRing ϖ)) (c : K) (m : K₀ → ℤ) (δ : Γ₀) (hδ : δ < 1)
    (hf : ∀ z : ↥(upperHalfPlane K₀ K), (z : K) ∈ affinoid ϖ 0 →
      (f : ↥(upperHalfPlane K₀ K) → K) z =
          c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * (1 + (h : ↥(upperHalfPlane K₀ K) → K) z) ∧
      Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) ≤ δ)
    (b : ↥(upperHalfPlane K₀ K)) (hb : (b : K) ∈ affinoid ϖ 0) :
    ∃ d : K, Valued.v d ≤ 1 ∧
      Valued.v (d - ∑ t ∈ T, (m t : K) / ((b : K) - algebraMap K₀ K t)) ≤ δ ∧
      ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((z : K) - (b : K)) < 1 →
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b * (1 + d * ((z : K) - (b : K))))
          ≤ Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) b) * Valued.v ((z : K) - (b : K)) ^ 2 := by
  classical

  have mem0 : ∀ w : K, w ∈ affinoid ϖ 0 ↔ Valued.v w ≤ 1 ∧
      ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → 1 ≤ Valued.v (w - algebraMap K₀ K a) := by
    intro w
    simp only [affinoid, Set.mem_setOf_eq, pow_zero]
  have vadd : ∀ x y : K, Valued.v y < Valued.v x → Valued.v (x + y) = Valued.v x := by
    intro x y hxy
    refine le_antisymm ((Valuation.map_add _ _ _).trans (max_le le_rfl hxy.le)) ?_
    by_contra hlt
    push_neg at hlt
    have h' : Valued.v x ≤ max (Valued.v (x + y)) (Valued.v y) := by
      have := Valuation.map_sub Valued.v (x + y) y
      simpa using this
    rcases le_max_iff.1 h' with h1 | h1
    · exact absurd h1 (not_le.2 hlt)
    · exact absurd h1 (not_le.2 hxy)
  obtain ⟨hb1, hb2⟩ := (mem0 (b : K)).1 hb
  have hbt : ∀ t ∈ T, Valued.v ((b : K) - algebraMap K₀ K t) = 1 := fun t ht =>
    le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hb1 (hT t ht))) (hb2 t (hT t ht))
  have hbt0 : ∀ t ∈ T, ((b : K) - algebraMap K₀ K t) ≠ 0 := fun t ht h0 => by
    have h1 := hbt t ht
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hdisc : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((z : K) - (b : K)) < 1 → (z : K) ∈ affinoid ϖ 0 := by
    intro z hz
    rw [mem0]
    constructor
    · have h1 : (z : K) = (b : K) + ((z : K) - (b : K)) := by ring
      rw [h1]
      exact Valuation.map_add_le _ hb1 hz.le
    · intro a ha
      have h1 := hb2 a ha
      have h2 : (z : K) - algebraMap K₀ K a = ((b : K) - algebraMap K₀ K a) + ((z : K) - (b : K)) := by ring
      rw [h2, vadd _ _ (lt_of_lt_of_le hz h1)]
      exact h1

  obtain ⟨e, he, hTay⟩ := CerednikDrinfeld.Omega.exists_v_sub_sub_mul_le_mul_sq_of_mem_affinoid_zero K₀ K ϖ h δ
    (fun z hz => (hf z hz).2) b hb
  have hhb : Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) b) ≤ δ := (hf b hb).2
  have h1hb : Valued.v (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) = 1 := LocCore.v_one_add_eq_one (lt_of_le_of_lt hhb hδ)
  have h1hb0 : (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at h1hb
    exact zero_ne_one h1hb

  refine ⟨(∑ t ∈ T, (m t : K) / ((b : K) - algebraMap K₀ K t)) + e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b), ?_, ?_, ?_⟩
  · refine Valuation.map_add_le _ (Valuation.map_sum_le _ fun t ht => ?_) ?_
    · rw [map_div₀, hbt t ht, div_one]
      exact LocCore.v_intCast_le_one (m t)
    · rw [map_div₀, h1hb, div_one]
      exact he.trans hδ.le
  · rw [add_sub_cancel_left, map_div₀, h1hb, div_one]
    exact he

  intro z hz
  have hzΩ : (z : K) ∈ affinoid ϖ 0 := hdisc z hz
  have hfz := (hf z hzΩ).1
  have hfb := (hf b hb).1

  set ε : K := (z : K) - (b : K) with hε
  set u : K₀ → K := fun t => ε / ((b : K) - algebraMap K₀ K t) with hu
  set x : K₀ → K := fun t => (1 + u t) ^ (m t) - 1 with hx
  set lin : K₀ → K := fun t => (m t : K) / ((b : K) - algebraMap K₀ K t) * ε with hlin
  set xh : K := ((h : ↥(upperHalfPlane K₀ K) → K) z - (h : ↥(upperHalfPlane K₀ K) → K) b) / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) with hxh
  set P : K := ∏ t ∈ T, (1 + x t) with hP
  set S : K := ∑ t ∈ T, x t with hS
  set L : K := ∑ t ∈ T, lin t with hL
  have hσ1 : Valued.v ε ≤ 1 := hz.le

  have hvu : ∀ t ∈ T, Valued.v (u t) = Valued.v ε := fun t ht => by
    simp only [hu]; rw [map_div₀, hbt t ht, div_one]
  have hfac : ∀ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t) = ((b : K) - algebraMap K₀ K t) ^ (m t) * (1 + x t) := by
    intro t ht
    have h1 : (z : K) - algebraMap K₀ K t = ((b : K) - algebraMap K₀ K t) * (1 + u t) := by
      simp only [hu, hε]
      field_simp [hbt0 t ht]
      ring
    rw [h1, mul_zpow]
    simp only [hx, add_sub_cancel]

  have hhfac : 1 + (h : ↥(upperHalfPlane K₀ K) → K) z = (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) * (1 + xh) := by
    simp only [hxh]
    field_simp [h1hb0]
    ring

  have hFz : (f : ↥(upperHalfPlane K₀ K) → K) z = (f : ↥(upperHalfPlane K₀ K) → K) b * (P * (1 + xh)) := by
    rw [hfz, hfb, Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, hhfac]
    simp only [hP]
    ring

  have hxlin : ∀ t ∈ T, Valued.v (x t - lin t) ≤ Valued.v ε * Valued.v ε := by
    intro t ht
    have h1 : x t - lin t = (1 + u t) ^ (m t) - 1 - (m t : K) * u t := by
      simp only [hx, hlin, hu]; ring
    rw [h1, ← pow_two, ← hvu t ht]
    exact LocCore.v_one_add_zpow_sub_le (u t) (by rw [hvu t ht]; exact hz) (m t)
  have hxle : ∀ t ∈ T, Valued.v (x t) ≤ Valued.v ε := by
    intro t ht
    have h1 : x t = (x t - lin t) + lin t := by ring
    rw [h1]
    refine Valuation.map_add_le _ ((hxlin t ht).trans ?_) ?_
    · calc Valued.v ε * Valued.v ε ≤ 1 * Valued.v ε := mul_le_mul' hσ1 le_rfl
        _ = Valued.v ε := one_mul _
    · simp only [hlin]
      rw [map_mul, map_div₀, hbt t ht, div_one]
      calc Valued.v (m t : K) * Valued.v ε ≤ 1 * Valued.v ε := mul_le_mul' (LocCore.v_intCast_le_one (m t)) le_rfl
        _ = Valued.v ε := one_mul _
  have hP1 : Valued.v (P - 1) ≤ Valued.v ε := LocCore.v_prod_one_add_sub_one_le T x hσ1 hxle
  have hPS : Valued.v (P - 1 - S) ≤ Valued.v ε * Valued.v ε := LocCore.v_prodRem_le T x hσ1 hxle
  have hnum : Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z - (h : ↥(upperHalfPlane K₀ K) → K) b - e * ε) ≤ δ * Valued.v ε ^ 2 := hTay z hz
  have hxhlin : Valued.v (xh - e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) * ε) ≤ Valued.v ε * Valued.v ε := by
    have h1 : xh - e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) * ε = ((h : ↥(upperHalfPlane K₀ K) → K) z - (h : ↥(upperHalfPlane K₀ K) → K) b - e * ε) / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) := by
      simp only [hxh]
      field_simp [h1hb0]
    rw [h1, map_div₀, h1hb, div_one]
    refine hnum.trans ?_
    rw [pow_two]
    calc δ * (Valued.v ε * Valued.v ε) ≤ 1 * (Valued.v ε * Valued.v ε) := mul_le_mul' hδ.le le_rfl
      _ = Valued.v ε * Valued.v ε := one_mul _
  have hxhle : Valued.v xh ≤ Valued.v ε := by
    have h1 : xh = (xh - e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) * ε) + e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) * ε := by ring
    rw [h1]
    refine Valuation.map_add_le _ (hxhlin.trans ?_) ?_
    · calc Valued.v ε * Valued.v ε ≤ 1 * Valued.v ε := mul_le_mul' hσ1 le_rfl
        _ = Valued.v ε := one_mul _
    · rw [map_mul, map_div₀, h1hb, div_one]
      calc Valued.v e * Valued.v ε ≤ 1 * Valued.v ε := mul_le_mul' (he.trans hδ.le) le_rfl
        _ = Valued.v ε := one_mul _

  have key : (f : ↥(upperHalfPlane K₀ K) → K) z - (f : ↥(upperHalfPlane K₀ K) → K) b * (1 + ((∑ t ∈ T, (m t : K) / ((b : K) - algebraMap K₀ K t)) + e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b)) * ((z : K) - (b : K))) =
      (f : ↥(upperHalfPlane K₀ K) → K) b * ((P - 1 - S) + ((P - 1) * xh + ((S - L) + (xh - e / (1 + (h : ↥(upperHalfPlane K₀ K) → K) b) * ε)))) := by
    rw [hFz, add_mul, Finset.sum_mul]
    simp only [hL, hlin, hε]
    ring
  rw [key, map_mul, pow_two]
  refine mul_le_mul' le_rfl ?_
  refine Valuation.map_add_le _ hPS (Valuation.map_add_le _ ?_ (Valuation.map_add_le _ ?_ hxhlin))
  · rw [map_mul]
    exact mul_le_mul' hP1 hxhle
  · have h1 : ∑ t ∈ T, (x t - lin t) = S - L := by
      simp only [hS, hL, Finset.sum_sub_distrib]
    rw [← h1]
    exact Valuation.map_sum_le _ hxlin

end S_CerednikDrinfeld_Omega_exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_v_sub_sum_div_sub_le_of_forall_eq_mul_prod_zpow_mul_one_add (solution)
