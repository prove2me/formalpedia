-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_eq_mul_prod_zpow_mul_one_add_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f48cdd48-9252-5d9a-ac06-d7e451e9ddbe

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit

set_option autoImplicit false

open Filter Polynomial
open scoped Topology
open CerednikDrinfeld.Omega

namespace P2mKcUnitsRes

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_eq_one_of_v_sub_one_lt {x : K} (h : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_one]), Valuation.map_one]

theorem v_mul_sub_one_le {x y : K} {δ : Γ₀} (hδ : δ < 1) (hx : Valued.v (x - 1) ≤ δ)
    (hy : Valued.v (y - 1) ≤ δ) : Valued.v (x * y - 1) ≤ δ := by
  have : x * y - 1 = (x - 1) * (y - 1) + ((x - 1) + (y - 1)) := by ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ((Valuation.map_add _ _ _).trans (max_le hx hy)))
  rw [Valuation.map_mul]
  calc Valued.v (x - 1) * Valued.v (y - 1) ≤ δ * 1 := mul_le_mul' hx (hy.trans hδ.le)
    _ = δ := mul_one δ

theorem v_inv_sub_one_le {x : K} {δ : Γ₀} (hδ : δ < 1) (hx : Valued.v (x - 1) ≤ δ) :
    Valued.v (x⁻¹ - 1) ≤ δ := by
  have hvx : Valued.v x = 1 := v_eq_one_of_v_sub_one_lt (lt_of_le_of_lt hx hδ)
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hvx; exact zero_ne_one hvx
  have : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by
    field_simp
    ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, hvx, inv_one, mul_one]
  exact hx

theorem v_multiset_prod_sub_one_le (s : Multiset K) {δ : Γ₀} (hδ : δ < 1)
    (h : ∀ x ∈ s, Valued.v (x - 1) ≤ δ) : Valued.v (s.prod - 1) ≤ δ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact v_mul_sub_one_le hδ (h a (Multiset.mem_cons_self a s))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

theorem v_div_sub_one_le {x y : K} {δ : Γ₀} (hδ : δ < 1) (hx : Valued.v (x - 1) ≤ δ)
    (hy : Valued.v (y - 1) ≤ δ) : Valued.v (x / y - 1) ≤ δ := by
  rw [div_eq_mul_inv]
  exact v_mul_sub_one_le hδ hx (v_inv_sub_one_le hδ hy)

section Factor

variable {ι : Type} (out : K → Prop) [DecidablePred out] (e : ι → K) (hole : K → ι)

def monoPart (z α : K) : K := if out α then -α else z - e (hole α)

theorem prod_map_hole_eq_prod_pow [DecidableEq ι] (T : Finset ι) (g : ι → K) (s : Multiset K)
    (hs : ∀ α ∈ s, hole α ∈ T) :
    (s.map fun α => g (hole α)).prod = ∏ t ∈ T, g t ^ Multiset.card (s.filter fun α => hole α = t) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have haT : hole a ∈ T := hs a (Multiset.mem_cons_self a s)
    rw [Multiset.map_cons, Multiset.prod_cons, ih fun α hα => hs α (Multiset.mem_cons_of_mem hα)]
    have hcard : ∀ t : ι, Multiset.card ((a ::ₘ s).filter fun α => hole α = t) =
        Multiset.card (s.filter fun α => hole α = t) + (if hole a = t then 1 else 0) := by
      intro t
      by_cases ht : hole a = t
      · rw [Multiset.filter_cons_of_pos (p := fun α => hole α = t) s ht, Multiset.card_cons, if_pos ht]
      · rw [Multiset.filter_cons_of_neg (p := fun α => hole α = t) s ht, if_neg ht, add_zero]
    have hrhs : (∏ t ∈ T, g t ^ Multiset.card ((a ::ₘ s).filter fun α => hole α = t)) =
        (∏ t ∈ T, g t ^ Multiset.card (s.filter fun α => hole α = t)) *
          ∏ t ∈ T, (if hole a = t then g t else 1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [hcard t, pow_add]
      split_ifs <;> simp
    rw [hrhs, Finset.prod_ite_eq T (hole a) g, if_pos haT, mul_comm]

theorem prod_map_sub_eq [DecidableEq ι] (T : Finset ι) (s : Multiset K) (z : K)
    (hs : ∀ α ∈ s, ¬ out α → hole α ∈ T) (hμ : ∀ α ∈ s, monoPart out e hole z α ≠ 0) :
    (s.map fun α => z - α).prod =
      ((s.filter out).map fun α => -α).prod *
        (∏ t ∈ T, (z - e t) ^ Multiset.card ((s.filter fun α => ¬ out α).filter fun α => hole α = t)) *
          (s.map fun α => (z - α) / monoPart out e hole z α).prod := by
  have h1 : (s.map fun α => z - α).prod =
      (s.map fun α => monoPart out e hole z α * ((z - α) / monoPart out e hole z α)).prod := by
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => ?_)
    rw [mul_comm, div_mul_cancel₀ _ (hμ α hα)]
  have h2 : (s.map fun α => monoPart out e hole z α).prod =
      ((s.filter out).map fun α => monoPart out e hole z α).prod *
        ((s.filter fun α => ¬ out α).map fun α => monoPart out e hole z α).prod := by
    rw [← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not]
  have h3 : ((s.filter out).map fun α => monoPart out e hole z α).prod = ((s.filter out).map fun α => -α).prod :=
    congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => by
      rw [monoPart, if_pos (Multiset.mem_filter.1 hα).2])
  have h4 : ((s.filter fun α => ¬ out α).map fun α => monoPart out e hole z α).prod =
      ((s.filter fun α => ¬ out α).map fun α => z - e (hole α)).prod :=
    congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => by
      rw [monoPart, if_neg (Multiset.mem_filter.1 hα).2])
  rw [h1, Multiset.prod_map_mul, h2, h3, h4,
    prod_map_hole_eq_prod_pow hole T (fun t => z - e t) _ fun α hα =>
      hs α (Multiset.mem_filter.1 hα).1 (Multiset.mem_filter.1 hα).2]

end Factor

section Omega

variable {K₀ : Type} [Field K₀] [Algebra K₀ K] (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem one_le_inv_p : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le

theorem mem_affinoid_one_iff (z : K) :
    z ∈ affinoid ϖ 1 ↔ Valued.v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ∧
      ∀ a : K₀, Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ Valued.v (z - algebraMap K₀ K a) := by
  rw [mem_affinoid_iff', pow_one, pow_one]

theorem inv_p_le_of_one_lt
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    {a : K₀} (ha : 1 < Valued.v (algebraMap K₀ K a)) :
    (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ≤ Valued.v (algebraMap K₀ K a) := by
  have ha0 : algebraMap K₀ K a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at ha
    exact not_lt.2 zero_le' ha
  have hva0 : 0 < Valued.v (algebraMap K₀ K a) := (Valuation.pos_iff _).2 ha0
  rcases hunif a⁻¹ with h | h
  · rw [map_inv₀, map_inv₀] at h
    rwa [inv_le_comm₀ ϖ.pos hva0]
  · rw [map_inv₀, map_inv₀, one_le_inv₀ hva0] at h
    exact absurd h (not_le.2 ha)

theorem exists_v_sub_le_p
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    {a : K₀} (ha : Valued.v (algebraMap K₀ K a) ≤ 1) :
    ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) := by
  obtain ⟨t, ht, hlt⟩ := hTcov a ha
  refine ⟨t, ht, ?_⟩
  rcases hunif (a - t) with h | h
  · rwa [map_sub] at h
  · rw [map_sub] at h
    exact absurd h (not_le.2 hlt)

theorem mem_affinoid_one_of_star
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    {z : K} (hzt : ∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v (z - algebraMap K₀ K t))
    (hz : Valued.v z < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹) : z ∈ affinoid ϖ 1 := by
  rw [mem_affinoid_one_iff]
  refine ⟨hz.le, fun a => ?_⟩
  rcases le_or_gt (Valued.v (algebraMap K₀ K a)) 1 with ha | ha
  · obtain ⟨t, ht, hat⟩ := exists_v_sub_le_p ϖ hunif T hTcov ha
    have hlt : Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < Valued.v (z - algebraMap K₀ K t) :=
      lt_of_le_of_lt hat (hzt t ht)
    have : z - algebraMap K₀ K a = (z - algebraMap K₀ K t) - (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ hlt]
    exact (hzt t ht).le
  · have hbig := inv_p_le_of_one_lt ϖ hunif ha
    have hlt : Valued.v z < Valued.v (algebraMap K₀ K a) := lt_of_lt_of_le hz hbig
    rw [Valuation.map_sub_eq_of_lt_right _ hlt]
    exact ϖ.lt_one.le.trans ((one_le_inv_p ϖ).trans hbig)

theorem far_or_hole_of_not_mem
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    {α : K} (hα : α ∉ affinoid ϖ 1) :
    (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ≤ Valued.v α ∨
      ∃ t ∈ T, Valued.v (α - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) := by
  rw [mem_affinoid_one_iff, not_and_or] at hα
  rcases hα with h | h
  · exact Or.inl (not_le.1 h).le
  · push Not at h
    obtain ⟨a, ha⟩ := h
    rcases le_or_gt (Valued.v (algebraMap K₀ K a)) 1 with ha1 | ha1
    · obtain ⟨t, ht, hat⟩ := exists_v_sub_le_p ϖ hunif T hTcov ha1
      refine Or.inr ⟨t, ht, ?_⟩
      have : α - algebraMap K₀ K t = (α - algebraMap K₀ K a) + (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le ha.le hat)
    · have hbig := inv_p_le_of_one_lt ϖ hunif ha1
      refine Or.inl ?_
      have hlt : Valued.v (α - algebraMap K₀ K a) < Valued.v (algebraMap K₀ K a) :=
        ha.trans (lt_of_lt_of_le (lt_of_lt_of_le ϖ.lt_one (one_le_inv_p ϖ)) hbig)
      have : α = (α - algebraMap K₀ K a) + algebraMap K₀ K a := by ring
      rw [this, Valuation.map_add_eq_of_lt_right _ hlt]
      exact hbig

theorem sub_const_mem_holRing (t : K₀) :
    (fun z : ↥(upperHalfPlane K₀ K) => (z : K) - algebraMap K₀ K t) ∈ holRing ϖ := by
  intro n
  obtain ⟨B, -, hB1, hB2, -⟩ := exists_bound (algebraMap K₀ K (ϖ.ϖ⁻¹ ^ n)) (algebraMap K₀ K t)
  have h := isHolOn_ratPair (S := affinoid ϖ n) ⟨X - C (algebraMap K₀ K t), 1⟩ (fun z _ => by simp)
    ⟨B, fun z hz => by
      have h1 := ((mem_affinoid_iff' ϖ n z).1 hz).1
      have h2 : Valued.v z ≤ Valued.v B := by
        refine h1.trans (le_trans (le_of_eq ?_) hB1)
        rw [map_pow, map_inv₀, map_pow, map_inv₀]
      simpa [RatPair.evalAt] using (Valuation.map_sub _ _ _).trans (max_le h2 hB2)⟩
  convert h using 1
  funext z
  simp [restrictAffinoid, RatPair.evalAt]

theorem inv_sub_const_mem_holRing (t : K₀) :
    (fun z : ↥(upperHalfPlane K₀ K) => ((z : K) - algebraMap K₀ K t)⁻¹) ∈ holRing ϖ := by
  intro n
  have hne : ∀ z ∈ affinoid ϖ n, z - algebraMap K₀ K t ≠ 0 := fun z hz h0 => by
    have hzΩ := affinoid_subset_upperHalfPlane ϖ n hz
    rw [mem_upperHalfPlane_iff] at hzΩ
    exact hzΩ t (sub_eq_zero.1 h0).symm
  have h := isHolOn_ratPair (S := affinoid ϖ n) ⟨1, X - C (algebraMap K₀ K t)⟩ (fun z hz => by simpa using hne z hz)
    ⟨algebraMap K₀ K (ϖ.ϖ ^ n)⁻¹, fun z hz => by
      have h1 := ((mem_affinoid_iff' ϖ n z).1 hz).2 t
      have hpos : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := pow_pos ϖ.pos n
      simp only [RatPair.evalAt, eval_one, eval_sub, eval_X, eval_C, map_inv₀, map_pow, one_div]
      exact inv_anti₀ hpos h1⟩
  convert h using 1
  funext z
  simp [restrictAffinoid, RatPair.evalAt]

noncomputable def zpowSub (t : K₀) (n : ℤ) : ↥(holRing ϖ) :=
  if 0 ≤ n then (⟨_, sub_const_mem_holRing ϖ t⟩ : ↥(holRing ϖ)) ^ n.toNat
  else (⟨_, inv_sub_const_mem_holRing ϖ t⟩ : ↥(holRing ϖ)) ^ (-n).toNat

theorem coe_mul_apply (F G : ↥(holRing ϖ)) (w : ↥(upperHalfPlane K₀ K)) :
    ((F * G : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      (F : ↥(upperHalfPlane K₀ K) → K) w * (G : ↥(upperHalfPlane K₀ K) → K) w := rfl

theorem coe_pow_apply (F : ↥(holRing ϖ)) (n : ℕ) (w : ↥(upperHalfPlane K₀ K)) :
    ((F ^ n : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w = ((F : ↥(upperHalfPlane K₀ K) → K) w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, coe_mul_apply, ih, pow_succ]

theorem coe_prod_apply {ι : Type} (T : Finset ι) (F : ι → ↥(holRing ϖ)) (w : ↥(upperHalfPlane K₀ K)) :
    ((∏ t ∈ T, F t : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      ∏ t ∈ T, ((F t : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | insert a T ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, coe_mul_apply, ih]

theorem zpowSub_apply (t : K₀) (n : ℤ) (w : ↥(upperHalfPlane K₀ K)) :
    (zpowSub ϖ t n : ↥(upperHalfPlane K₀ K) → K) w = ((w : K) - algebraMap K₀ K t) ^ n := by
  unfold zpowSub
  split_ifs with hn
  · rw [coe_pow_apply]
    conv_rhs => rw [← Int.toNat_of_nonneg hn, zpow_natCast]
  · rw [coe_pow_apply]
    have hn' : 0 ≤ -n := by omega
    conv_rhs => rw [← neg_neg n, ← Int.toNat_of_nonneg hn', zpow_neg, zpow_natCast]
    simp [inv_pow]

end Omega

end P2mKcUnitsRes

open P2mKcUnitsRes in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (f : ↥(holRing ϖ)) (hf : IsUnit f) :
    ∃ (c : K) (m : K₀ → ℤ) (h : ↥(holRing ϖ)), c ≠ 0 ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
        Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ →
          (f : ↥(upperHalfPlane K₀ K) → K) z =
              c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * (1 + (h : ↥(upperHalfPlane K₀ K) → K) z) ∧
          Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) < 1) ∧
      ∀ ρ : Γ₀, Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ → ρ ≤ 1 →
        ∃ δ : Γ₀, δ < 1 ∧ ∀ z : ↥(upperHalfPlane K₀ K),
          (∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t)) → Valued.v (z : K) ≤ ρ⁻¹ →
            Valued.v ((h : ↥(upperHalfPlane K₀ K) → K) z) ≤ δ := by
  classical

  have hp0 : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) := ϖ.pos
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  have hP1 : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := one_le_inv_p ϖ
  have hϖ0 : algebraMap K₀ K ϖ.ϖ ≠ 0 := algebraMap_varpi_ne_zero ϖ
  have hΩ1 : affinoid ϖ 1 ⊆ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ 1

  have hstar1 : ∀ (ρ : Γ₀), Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ → ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t)) → Valued.v (z : K) ≤ ρ⁻¹ → (z : K) ∈ affinoid ϖ 1 := by
    intro ρ hρ z hzt hz
    refine mem_affinoid_one_of_star ϖ hunif T hTcov (fun t ht => lt_of_lt_of_le hρ (hzt t ht))
      (lt_of_le_of_lt hz ?_)
    exact (inv_lt_inv₀ (lt_trans hp0 hρ) hp0).2 hρ
  have hsub0 : ∀ (z : ↥(upperHalfPlane K₀ K)) (t : K₀), (z : K) - algebraMap K₀ K t ≠ 0 := fun z t h0 => by
    have hz := z.2
    rw [mem_upperHalfPlane_iff] at hz
    exact hz t (sub_eq_zero.1 h0).symm

  by_cases hne : ¬ (affinoid ϖ 1).Nonempty
  · refine ⟨1, 0, 0, one_ne_zero, fun z hzt hz => ?_, fun ρ hρ _ => ⟨0, zero_lt_one, fun z hzt hz => ?_⟩⟩
    · exact absurd ⟨(z : K), mem_affinoid_one_of_star ϖ hunif T hTcov hzt hz⟩ hne
    · exact absurd ⟨(z : K), hstar1 ρ hρ z hzt hz⟩ hne
  push Not at hne
  obtain ⟨z₁, hz₁⟩ := hne

  obtain ⟨g, hg⟩ := hf.exists_right_inv
  have hfg : ∀ w : ↥(upperHalfPlane K₀ K),
      (f : ↥(upperHalfPlane K₀ K) → K) w * (g : ↥(upperHalfPlane K₀ K) → K) w = 1 := fun w => by
    have := congrArg (fun F : ↥(holRing ϖ) => (F : ↥(upperHalfPlane K₀ K) → K) w) hg
    simpa [coe_mul_apply] using this
  obtain ⟨B, hB⟩ := (g.2 1).bounded
  obtain ⟨B', hB'0, hBB', -, h1B'⟩ := exists_bound B B
  have hvB' : 0 < Valued.v B' := (Valuation.pos_iff _).2 hB'0
  have hflow : ∀ w : K, ∀ hw : w ∈ affinoid ϖ 1,
      (Valued.v B')⁻¹ ≤ Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) := by
    intro w hw
    have h1 := congrArg Valued.v (hfg ⟨w, hΩ1 hw⟩)
    rw [Valuation.map_mul, Valuation.map_one] at h1
    have hgle : Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) ≤ Valued.v B' := (hB ⟨w, hw⟩).trans hBB'
    have hg0 : Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h1; exact zero_ne_one h1
    have : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) =
        (Valued.v ((g : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_anti₀ ((Valuation.pos_iff _).2 (by rwa [ne_eq, map_eq_zero] at hg0)) hgle
  have hf0 : ∀ w : K, ∀ hw : w ∈ affinoid ϖ 1, 0 < Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) :=
    fun w hw => lt_of_lt_of_le (inv_pos.2 hvB') (hflow w hw)

  obtain ⟨r, hrpf, -, hlim⟩ := f.2 1
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have hthr0 : vRestrict K (algebraMap K₀ K ϖ.ϖ * B'⁻¹) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact mul_ne_zero hϖ0 (inv_ne_zero hB'0)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hthr0))
  set R : RatPair K := r k with hRdef
  have happ : ∀ w : K, ∀ hw : w ∈ affinoid ϖ 1,
      Valued.v (R.evalAt w - (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) <
        Valued.v (algebraMap K₀ K ϖ.ϖ) * (Valued.v B')⁻¹ := by
    intro w hw
    have h1 : vRestrict K (R.evalAt w - restrictAffinoid ϖ 1 (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hw⟩) <
        vRestrict K (algebraMap K₀ K ϖ.ϖ * B'⁻¹) := by simpa using hk k le_rfl ⟨w, hw⟩
    rw [← v_lt_iff_vRestrict_lt, Valuation.map_mul, map_inv₀] at h1
    exact h1
  have happ' : ∀ w : K, ∀ hw : w ∈ affinoid ϖ 1,
      Valued.v (R.evalAt w - (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) <
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) := fun w hw =>
    (happ w hw).trans_le ((mul_le_of_le_one_left' hp1.le).trans (hflow w hw))
  have hvR : ∀ w : K, ∀ hw : w ∈ affinoid ϖ 1,
      Valued.v (R.evalAt w) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) := by
    intro w hw
    have : R.evalAt w = (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩ +
        (R.evalAt w - (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) := by ring
    rw [this]
    exact Valuation.map_add_eq_of_lt_left _ (happ' w hw)
  have hR0 : ∀ w : K, w ∈ affinoid ϖ 1 → R.evalAt w ≠ 0 := fun w hw h0 => by
    have := hf0 w hw
    rw [← hvR w hw, h0, map_zero] at this
    exact lt_irrefl _ this

  have hquot : ∀ w : K, ∀ hw : w ∈ affinoid ϖ 1,
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩ / R.evalAt w - 1) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) := by
    intro w hw
    have hfw := hf0 w hw
    have : (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩ / R.evalAt w - 1 =
        -(R.evalAt w - (f : ↥(upperHalfPlane K₀ K) → K) ⟨w, hΩ1 hw⟩) / R.evalAt w := by
      field_simp [hR0 w hw]
      ring
    rw [this, map_div₀, Valuation.map_neg, hvR w hw, div_le_iff₀ hfw]
    refine (happ w hw).le.trans (mul_le_mul' le_rfl (hflow w hw))

  have hnum0 : R.num ≠ 0 := fun h0 => hR0 z₁ hz₁ (by simp [RatPair.evalAt, h0])
  have hden0 : R.den ≠ 0 := fun h0 => by
    have := hrpf k z₁ hz₁
    rw [← hRdef, h0, eval_zero] at this
    exact this rfl
  have hroots : ∀ α ∈ R.num.roots + R.den.roots, α ∉ affinoid ϖ 1 := by
    intro α hα hαS
    rcases Multiset.mem_add.1 hα with hα | hα
    · have hev : R.num.eval α = 0 := (mem_roots hnum0).1 hα
      exact hR0 α hαS (by rw [RatPair.evalAt, hev, zero_div])
    · exact hrpf k α hαS ((mem_roots hden0).1 hα)

  let out : K → Prop := fun α => (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ≤ Valued.v α
  let hole : K → K₀ := fun α =>
    if hh : ∃ t ∈ T, Valued.v (α - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) then hh.choose else 0
  have hhole : ∀ α ∈ R.num.roots + R.den.roots, ¬ out α →
      hole α ∈ T ∧ Valued.v (α - algebraMap K₀ K (hole α)) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) := by
    intro α hα hout
    have hh : ∃ t ∈ T, Valued.v (α - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) :=
      (far_or_hole_of_not_mem ϖ hunif T hTcov (hroots α hα)).resolve_left hout
    simp only [hole, dif_pos hh]
    exact hh.choose_spec
  have hout0 : ∀ α : K, out α → α ≠ 0 := fun α hα h0 => by
    have : (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ≤ 0 := by simpa [out, h0] using hα
    exact not_lt.2 this (lt_of_lt_of_le zero_lt_one hP1)
  let e : K₀ → K := fun t => algebraMap K₀ K t

  let a_ : K₀ → ℕ := fun t => Multiset.card ((R.num.roots.filter fun α => ¬ out α).filter fun α => hole α = t)
  let b_ : K₀ → ℕ := fun t => Multiset.card ((R.den.roots.filter fun α => ¬ out α).filter fun α => hole α = t)
  let m : K₀ → ℤ := fun t => (a_ t : ℤ) - (b_ t : ℤ)
  let cn : K := R.num.leadingCoeff * ((R.num.roots.filter out).map fun α => -α).prod
  let cd : K := R.den.leadingCoeff * ((R.den.roots.filter out).map fun α => -α).prod
  have hcn0 : cn ≠ 0 := by
    refine mul_ne_zero (leadingCoeff_ne_zero.2 hnum0) (Multiset.prod_ne_zero fun h0 => ?_)
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.1 h0
    exact hout0 α (Multiset.mem_filter.1 hα).2 (neg_eq_zero.1 hα0)
  have hcd0 : cd ≠ 0 := by
    refine mul_ne_zero (leadingCoeff_ne_zero.2 hden0) (Multiset.prod_ne_zero fun h0 => ?_)
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.1 h0
    exact hout0 α (Multiset.mem_filter.1 hα).2 (neg_eq_zero.1 hα0)
  let c : K := cn / cd
  have hc0 : c ≠ 0 := div_ne_zero hcn0 hcd0

  let U : K → K := fun z =>
    (R.num.roots.map fun α => (z - α) / monoPart out e hole z α).prod /
      (R.den.roots.map fun α => (z - α) / monoPart out e hole z α).prod

  have hμ0 : ∀ (z : ↥(upperHalfPlane K₀ K)) (α : K), α ∈ R.num.roots + R.den.roots →
      monoPart out e hole (z : K) α ≠ 0 := by
    intro z α hα
    by_cases hα' : out α
    · rw [monoPart, if_pos hα']; exact neg_ne_zero.2 (hout0 α hα')
    · rw [monoPart, if_neg hα']; exact hsub0 z _
  have hfact : ∀ z : ↥(upperHalfPlane K₀ K),
      R.evalAt z = c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * U z := by
    intro z
    have hn := prod_map_sub_eq out e hole T R.num.roots (z : K)
      (fun α hα hout => (hhole α (Multiset.mem_add.2 (Or.inl hα)) hout).1)
      (fun α hα => hμ0 z α (Multiset.mem_add.2 (Or.inl hα)))
    have hd := prod_map_sub_eq out e hole T R.den.roots (z : K)
      (fun α hα hout => (hhole α (Multiset.mem_add.2 (Or.inr hα)) hout).1)
      (fun α hα => hμ0 z α (Multiset.mem_add.2 (Or.inr hα)))
    have hzpow : (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) =
        (∏ t ∈ T, ((z : K) - e t) ^ a_ t) / ∏ t ∈ T, ((z : K) - e t) ^ b_ t := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [zpow_sub₀ (hsub0 z t), zpow_natCast, zpow_natCast]
    rw [RatPair.evalAt, (IsAlgClosed.splits R.num).eval_eq_prod_roots, (IsAlgClosed.splits R.den).eval_eq_prod_roots,
      hn, hd, hzpow]
    simp only [c, cn, cd, U]
    rw [div_mul_div_comm, div_mul_div_comm]
    congr 1 <;> ring

  have hUest : ∀ (ρ : Γ₀), Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ → ρ ≤ 1 → ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t)) → Valued.v (z : K) ≤ ρ⁻¹ →
        Valued.v (U z - 1) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ := by
    intro ρ hρ hρ1 z hzt hz
    have hρ0 : 0 < ρ := lt_trans hp0 hρ
    have hδ1 : Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hρ0, one_mul]; exact hρ

    have hunit : ∀ α ∈ R.num.roots + R.den.roots,
        Valued.v (((z : K) - α) / monoPart out e hole (z : K) α - 1) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ := by
      intro α hα
      by_cases hα' : out α
      · have hα0 := hout0 α hα'
        have : ((z : K) - α) / monoPart out e hole (z : K) α - 1 = (z : K) / (-α) := by
          rw [monoPart, if_pos hα']
          field_simp
          ring
        rw [this, map_div₀, Valuation.map_neg, div_le_iff₀ ((Valuation.pos_iff _).2 hα0)]
        refine hz.trans ?_
        calc ρ⁻¹ = Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := by
              rw [mul_comm (Valued.v _), mul_assoc, mul_inv_cancel₀ hp0.ne', mul_one]
          _ ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ * Valued.v α := mul_le_mul' le_rfl hα'
      · obtain ⟨hT', hle⟩ := hhole α hα hα'
        have hzt' := hzt (hole α) hT'
        have hne := hsub0 z (hole α)
        have : ((z : K) - α) / monoPart out e hole (z : K) α - 1 =
            -(α - algebraMap K₀ K (hole α)) / ((z : K) - algebraMap K₀ K (hole α)) := by
          simp only [monoPart, if_neg hα', e]
          field_simp
          ring
        rw [this, map_div₀, Valuation.map_neg, div_le_iff₀ (lt_of_lt_of_le hρ0 hzt')]
        refine hle.trans ?_
        calc Valued.v (algebraMap K₀ K ϖ.ϖ) = Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ * ρ := by
              rw [mul_assoc, inv_mul_cancel₀ hρ0.ne', mul_one]
          _ ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ * Valued.v ((z : K) - algebraMap K₀ K (hole α)) :=
              mul_le_mul' le_rfl hzt'
    have hA := v_multiset_prod_sub_one_le (R.num.roots.map fun α => ((z : K) - α) / monoPart out e hole (z : K) α)
      hδ1 (fun x hx => by
        obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
        exact hunit α (Multiset.mem_add.2 (Or.inl hα)))
    have hBB := v_multiset_prod_sub_one_le (R.den.roots.map fun α => ((z : K) - α) / monoPart out e hole (z : K) α)
      hδ1 (fun x hx => by
        obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
        exact hunit α (Multiset.mem_add.2 (Or.inr hα)))
    exact v_div_sub_one_le hδ1 hA hBB

  let E : ↥(holRing ϖ) := ∏ t ∈ T, zpowSub ϖ t (-(m t))
  let hh : ↥(holRing ϖ) := algebraMap K ↥(holRing ϖ) c⁻¹ * f * E - 1
  have hPne : ∀ z : ↥(upperHalfPlane K₀ K), (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) ≠ 0 := fun z =>
    Finset.prod_ne_zero_iff.2 fun t _ => zpow_ne_zero _ (hsub0 z t)
  have hEapply : ∀ z : ↥(upperHalfPlane K₀ K),
      (E : ↥(upperHalfPlane K₀ K) → K) z = (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t))⁻¹ := by
    intro z
    simp only [E]
    rw [coe_prod_apply, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [zpowSub_apply, zpow_neg]
  have hhapply : ∀ z : ↥(upperHalfPlane K₀ K), (hh : ↥(upperHalfPlane K₀ K) → K) z =
      (f : ↥(upperHalfPlane K₀ K) → K) z / (c * ∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) - 1 := by
    intro z
    show ((algebraMap K ↥(holRing ϖ) c⁻¹ * f * E : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) z - 1 = _
    rw [coe_mul_apply, coe_mul_apply, algebraMap_holRing_apply, hEapply]
    field_simp

  have hident : ∀ z : ↥(upperHalfPlane K₀ K), (f : ↥(upperHalfPlane K₀ K) → K) z =
      c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * (1 + (hh : ↥(upperHalfPlane K₀ K) → K) z) := by
    intro z
    rw [hhapply]
    have hP := hPne z
    field_simp
    ring

  have hcore : ∀ (ρ : Γ₀), Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ → ρ ≤ 1 → ∀ z : ↥(upperHalfPlane K₀ K),
      (∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t)) → Valued.v (z : K) ≤ ρ⁻¹ →
        Valued.v ((hh : ↥(upperHalfPlane K₀ K) → K) z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ := by
    intro ρ hρ hρ1 z hzt hz
    have hρ0 : 0 < ρ := lt_trans hp0 hρ
    have hδ1 : Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ < 1 := by
      rw [mul_inv_lt_iff₀ hρ0, one_mul]; exact hρ
    have hpδ : Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹ :=
      le_mul_of_one_le_right zero_le' ((one_le_inv₀ hρ0).2 hρ1)
    have hz1 : (z : K) ∈ affinoid ϖ 1 := hstar1 ρ hρ z hzt hz
    have hzeq : (⟨(z : K), hΩ1 hz1⟩ : ↥(upperHalfPlane K₀ K)) = z := rfl

    have hRz : R.evalAt z = c * (∏ t ∈ T, ((z : K) - algebraMap K₀ K t) ^ (m t)) * U z := hfact z
    have hUz0 : U z ≠ 0 := fun h0 => hR0 z hz1 (by rw [hRz, h0, mul_zero])
    have hrew : (hh : ↥(upperHalfPlane K₀ K) → K) z =
        ((f : ↥(upperHalfPlane K₀ K) → K) z / R.evalAt z) * U z - 1 := by
      rw [hhapply, hRz]
      field_simp
    rw [hrew]
    have hq := hquot z hz1
    rw [hzeq] at hq
    exact v_mul_sub_one_le hδ1 (hq.trans hpδ) (hUest ρ hρ hρ1 z hzt hz)
  refine ⟨c, m, hh, hc0, fun z hzt hz => ⟨hident z, ?_⟩, fun ρ hρ hρ1 =>
    ⟨Valued.v (algebraMap K₀ K ϖ.ϖ) * ρ⁻¹, by rw [mul_inv_lt_iff₀ (lt_trans hp0 hρ), one_mul]; exact hρ,
      fun z hzt hz => hcore ρ hρ hρ1 z hzt hz⟩⟩

  have hvz0 : 0 < Valued.v (z : K) := (Valuation.pos_iff _).2 fun h0 => by
    have hz2 := z.2
    rw [mem_upperHalfPlane_iff] at hz2
    exact hz2 0 (by rw [map_zero]; exact h0.symm)
  let D : Finset Γ₀ := insert 1 (insert (Valued.v (z : K))⁻¹ (T.image fun t => Valued.v ((z : K) - algebraMap K₀ K t)))
  have hDne : D.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  set ρ := D.min' hDne with hρdef
  have hρle : ∀ x ∈ D, ρ ≤ x := fun x hx => Finset.min'_le D x hx
  have hρmem : ρ ∈ D := Finset.min'_mem D hDne
  have hρ1 : ρ ≤ 1 := hρle 1 (Finset.mem_insert_self _ _)
  have hρt : ∀ t ∈ T, ρ ≤ Valued.v ((z : K) - algebraMap K₀ K t) := fun t ht =>
    hρle _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht)))
  have hpρ : Valued.v (algebraMap K₀ K ϖ.ϖ) < ρ := by
    rcases Finset.mem_insert.1 hρmem with h | h
    · rw [h]; exact hp1
    · rcases Finset.mem_insert.1 h with h | h
      · rw [h]; rwa [lt_inv_comm₀ hp0 hvz0]
      · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
        rw [← hteq]; exact hzt t ht
  have hρ0 : 0 < ρ := lt_trans hp0 hpρ
  have hρz : Valued.v (z : K) ≤ ρ⁻¹ := by
    have := hρle _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    rwa [le_inv_comm₀ hvz0 hρ0]
  refine lt_of_le_of_lt (hcore ρ hpρ hρ1 z hρt hρz) ?_
  rw [mul_inv_lt_iff₀ hρ0, one_mul]
  exact hpρ

end S_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_eq_mul_prod_zpow_mul_one_add_of_isUnit (solution)
