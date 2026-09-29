-- Prove2me | solution 1 for CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f83b62e5-26a5-5603-8a69-bf678f8bb192

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Filter
open CerednikDrinfeld.Omega

namespace P2mKcAffZeros

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem eq_one_of_prod_eq_one {s : Multiset Γ₀} (hle : ∀ x ∈ s, x ≤ 1) (hprod : s.prod = 1) :
    ∀ x ∈ s, x = 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    intro x hx
    rw [Multiset.prod_cons] at hprod
    have ha : a ≤ 1 := hle a (Multiset.mem_cons_self a s)
    have hs : s.prod ≤ 1 := by
      have := Multiset.prod_map_le_prod_map (s := s) id (fun _ => (1 : Γ₀))
        fun y hy => hle y (Multiset.mem_cons_of_mem hy)
      simpa using this
    have ha1 : a = 1 := by
      by_contra hne
      have hlt : a < 1 := lt_of_le_of_ne ha hne
      have : a * s.prod < 1 := mul_lt_one_of_lt_of_le hlt hs
      exact this.ne hprod
    rw [ha1, one_mul] at hprod
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha1
    · exact ih (fun y hy => hle y (Multiset.mem_cons_of_mem hy)) hprod x hx

theorem exists_generic_unit [IsAlgClosed K] (T : Multiset K) (hT : ∀ b ∈ T, Valued.v b ≤ 1) :
    ∃ u : K, Valued.v u = 1 ∧ ∀ b ∈ T, Valued.v (u - b) = 1 := by
  set T' : Multiset K := 0 ::ₘ T with hT'
  have hT'le : ∀ b ∈ T', Valued.v b ≤ 1 := fun b hb => by
    rcases Multiset.mem_cons.1 hb with rfl | hb
    · simp
    · exact hT b hb
  set F : K[X] := (T'.map fun b => X - C b).prod + 1 with hF
  have hmonic : (T'.map fun b => X - C b).prod.Monic := by
    refine monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  have hdegprod : (T'.map fun b => X - C b).prod.natDegree = Multiset.card T' := by
    rw [natDegree_multiset_prod_of_monic]
    · simp
    · intro f hf
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hf
      exact monic_X_sub_C b
  have hcard : 0 < Multiset.card T' := by rw [hT', Multiset.card_cons]; omega
  have hFdeg : F.degree ≠ 0 := by
    have h1 : F.natDegree = Multiset.card T' := by
      rw [hF, natDegree_add_eq_left_of_degree_lt, hdegprod]
      rw [degree_one, degree_eq_natDegree hmonic.ne_zero, hdegprod]
      exact_mod_cast hcard
    intro h0
    have := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
    omega
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root F hFdeg
  have hprod : (T'.map fun b => u - b).prod = -1 := by
    have h := hu
    rw [IsRoot, hF, eval_add, eval_one, eval_multiset_prod, Multiset.map_map, add_eq_zero_iff_eq_neg] at h
    convert h using 2 <;> try rfl
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  have hvprod : (T'.map fun b => Valued.v (u - b)).prod = 1 := by
    have := congrArg Valued.v hprod
    rw [Valuation.map_neg, Valuation.map_one, map_multiset_prod, Multiset.map_map] at this
    exact this
  have hule : Valued.v u ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hfac : ∀ b ∈ T', Valued.v (u - b) = Valued.v u := fun b hb =>
      Valuation.map_sub_eq_of_lt_left _ ((hT'le b hb).trans_lt hgt)
    have : (T'.map fun b => Valued.v (u - b)).prod = (T'.map fun _ => Valued.v u).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl hfac)
    rw [hvprod, Multiset.map_const', Multiset.prod_replicate] at this
    have h1 : (1 : Γ₀) < Valued.v u ^ Multiset.card T' := one_lt_pow₀ hgt hcard.ne'
    exact h1.ne this
  have hfacle : ∀ x ∈ T'.map (fun b => Valued.v (u - b)), x ≤ 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    exact (Valuation.map_sub _ _ _).trans (max_le hule (hT'le b hb))
  have hall := eq_one_of_prod_eq_one hfacle hvprod
  have hone : ∀ b ∈ T', Valued.v (u - b) = 1 := fun b hb => hall _ (Multiset.mem_map_of_mem _ hb)
  refine ⟨u, ?_, fun b hb => hone b (Multiset.mem_cons_of_mem hb)⟩
  have := hone 0 (Multiset.mem_cons_self 0 T)
  rwa [sub_zero] at this

theorem exists_generic_unit' [IsAlgClosed K] (T : Multiset K) :
    ∃ u : K, Valued.v u = 1 ∧ ∀ b ∈ T, 1 ≤ Valued.v (u - b) := by
  classical
  obtain ⟨u, hu1, hu⟩ := exists_generic_unit (T.filter fun b => Valued.v b ≤ 1)
    (fun b hb => (Multiset.mem_filter.1 hb).2)
  refine ⟨u, hu1, fun b hb => ?_⟩
  rcases le_or_gt (Valued.v b) 1 with h | h
  · exact (hu b (Multiset.mem_filter.2 ⟨hb, h⟩)).ge
  · rw [Valuation.map_sub_eq_of_lt_right _ (hu1.trans_lt h)]; exact h.le

theorem exists_generic_point [IsAlgClosed K] (c : K) {R : K} (hR : R ≠ 0) (A : Multiset K) :
    ∃ w : K, v (w - c) = v R ∧ ∀ a ∈ A, v R ≤ v (w - a) := by
  obtain ⟨u, hu1, hu⟩ := exists_generic_unit' (K := K) (A.map fun a => (a - c) / R)
  refine ⟨c + R * u, ?_, fun a ha => ?_⟩
  · rw [show c + R * u - c = R * u by ring, map_mul, hu1, mul_one]
  · have h1 := hu _ (Multiset.mem_map.2 ⟨a, ha, rfl⟩)
    have : c + R * u - a = R * (u - (a - c) / R) := by field_simp; ring
    rw [this, map_mul]
    calc v R = v R * 1 := (mul_one _).symm
      _ ≤ v R * v (u - (a - c) / R) := mul_le_mul' le_rfl h1

theorem good_of_near {c R : K} {A : Finset K} {z w : K}
    (hz : v (z - c) = v R) (hzA : ∀ a ∈ A, v R ≤ v (z - a)) (hw : v (w - z) < v R) :
    v (w - c) = v R ∧ ∀ a ∈ A, v R ≤ v (w - a) := by
  constructor
  · have : w - c = (w - z) + (z - c) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rw [hz]; exact hw), hz]
  · intro a ha
    have : w - a = (w - z) + (z - a) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (hw.trans_le (hzA a ha))]
    exact hzA a ha

section Aff

variable {K₀ : Type} [Field K₀] [Algebra K₀ K] (ϖ : PseudoUniformizer K₀ K) (n : ℕ)

structure Centres (T₀ : Finset K) : Prop where
  size : ∀ t ∈ T₀, v t ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n
  cover : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n → ∃ t ∈ T₀, Valued.v (algebraMap K₀ K a - t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n
  rat : ∀ t ∈ T₀, ∃ a : K₀, algebraMap K₀ K a = t

variable {ϖ n}

theorem p_pos : 0 < (Valued.v (algebraMap K₀ K ϖ.ϖ)) := ϖ.pos
theorem p_le_one : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ≤ 1 := ϖ.lt_one.le
theorem one_le_P : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 (p_le_one (ϖ := ϖ))
theorem pn_le_Pn : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
  (pow_le_one₀ zero_le' (p_le_one (ϖ := ϖ))).trans (one_le_pow₀ (one_le_P (ϖ := ϖ)))
theorem pn_pos : 0 < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := pow_pos (p_pos (ϖ := ϖ)) n

theorem exists_centres [DecidableEq K]
    (hfin : ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) :
    ∃ T₀ : Finset K, Centres ϖ n T₀ := by
  obtain ⟨T, hT⟩ := hfin
  refine ⟨(T.image (algebraMap K₀ K)).filter fun t => v t ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n, ⟨fun t ht => (Finset.mem_filter.1 ht).2,
    fun a ha => ?_, fun t ht => ?_⟩⟩
  · obtain ⟨t, htT, ht⟩ := hT a ha
    refine ⟨algebraMap K₀ K t, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨t, htT, rfl⟩, ?_⟩, ht⟩
    have : algebraMap K₀ K t = algebraMap K₀ K a - (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (ht.le.trans (pn_le_Pn (ϖ := ϖ))))
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 ht).1
    exact ⟨a, rfl⟩

variable {T₀ : Finset K} (hT : Centres ϖ n T₀)
include hT

theorem mem_affinoid_of {z : K} (hz : v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) (hzT : ∀ t ∈ T₀, (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v (z - t)) : z ∈ affinoid ϖ n := by
  rw [mem_affinoid_iff']
  refine ⟨hz, fun a => ?_⟩
  rcases le_or_gt (Valued.v (algebraMap K₀ K a)) ((Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) with ha | ha
  · obtain ⟨t, ht, hat⟩ := hT.cover a ha
    have h1 : v (algebraMap K₀ K a - t) < v (z - t) := hat.trans_le (hzT t ht)
    have : z - algebraMap K₀ K a = (z - t) - (algebraMap K₀ K a - t) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ h1]
    exact hzT t ht
  · have h1 : v z < v (algebraMap K₀ K a) := hz.trans_lt ha
    rw [Valuation.map_sub_eq_of_lt_right _ h1]
    exact (pn_le_Pn (ϖ := ϖ)).trans ha.le

theorem of_mem_affinoid {z : K} (hz : z ∈ affinoid ϖ n) : v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n ∧ ∀ t ∈ T₀, (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v (z - t) := by
  rw [mem_affinoid_iff'] at hz
  refine ⟨hz.1, fun t ht => ?_⟩
  obtain ⟨a, rfl⟩ := hT.rat t ht
  exact hz.2 a

theorem good_mem {t : K} (ht : t ∈ T₀) {e : K} (he1 : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v e) (he2 : v e ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n)
    {z : K} (hz : v (z - t) = v e) (hzT : ∀ t' ∈ T₀, v e ≤ v (z - t')) : z ∈ affinoid ϖ n := by
  refine mem_affinoid_of hT ?_ fun t' ht' => he1.trans (hzT t' ht')
  have : z = (z - t) + t := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le (hz.le.trans he2) (hT.size t ht))

variable [DecidableEq K]

variable (ϖ n) in
omit hT in

def crit (T₀ : Finset K) (t : K) : Finset K :=
  insert ((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ n) (insert (algebraMap K₀ K ϖ.ϖ ^ n)
    ((T₀.filter fun t' => (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v (t - t')).image fun t' => t - t'))

omit hT in
theorem mem_crit_of {t t' : K} (ht' : t' ∈ T₀) (h : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v (t - t')) : t - t' ∈ crit ϖ n T₀ t :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨t', Finset.mem_filter.2 ⟨ht', h⟩, rfl⟩))

omit hT in
theorem Pn_mem_crit (t : K) : (algebraMap K₀ K ϖ.ϖ)⁻¹ ^ n ∈ crit ϖ n T₀ t := Finset.mem_insert_self _ _

omit hT in
theorem pn_mem_crit (t : K) : algebraMap K₀ K ϖ.ϖ ^ n ∈ crit ϖ n T₀ t :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

omit hT in
theorem v_Pn : v ((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ n) = (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := by rw [map_pow, map_inv₀]

omit hT in
theorem v_pn : v (algebraMap K₀ K ϖ.ϖ ^ n) = (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := by rw [map_pow]

theorem crit_bounds {t : K} (ht : t ∈ T₀) {e : K} (he : e ∈ crit ϖ n T₀ t) :
    e ≠ 0 ∧ (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v e ∧ v e ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := by
  have key : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v e ∧ v e ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := by
    rcases Finset.mem_insert.1 he with rfl | he
    · rw [v_Pn]; exact ⟨pn_le_Pn (ϖ := ϖ), le_rfl⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · rw [v_pn]; exact ⟨le_rfl, pn_le_Pn (ϖ := ϖ)⟩
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 he
    obtain ⟨ht'T, h⟩ := Finset.mem_filter.1 ht'
    exact ⟨h, (Valuation.map_sub _ _ _).trans (max_le (hT.size t ht) (hT.size t' ht'T))⟩
  refine ⟨fun h0 => ?_, key⟩
  rw [h0, map_zero] at key
  exact (pn_pos (ϖ := ϖ) (n := n)).not_ge key.1

theorem region_mem {t : K} (ht : t ∈ T₀) {eh el : K} (heh : eh ∈ crit ϖ n T₀ t) (hel : el ∈ crit ϖ n T₀ t)
    (hcons : ∀ e ∈ crit ϖ n T₀ t, ¬ (v el < v e ∧ v e < v eh))
    {z : K} (hz1 : v el < v (z - t)) (hz2 : v (z - t) < v eh) : z ∈ affinoid ϖ n := by
  obtain ⟨-, hel1, -⟩ := crit_bounds hT ht hel
  obtain ⟨-, -, heh2⟩ := crit_bounds hT ht heh
  refine mem_affinoid_of hT ?_ fun t' ht' => ?_
  · have : z = (z - t) + t := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hz2.le.trans heh2) (hT.size t ht))
  · have hzt : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n < v (z - t) := hel1.trans_lt hz1
    rcases lt_or_ge (v (t - t')) ((Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) with h | h
    · have : z - t' = (z - t) + (t - t') := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (h.trans hzt)]
      exact hzt.le
    · have hmem := mem_crit_of (ϖ := ϖ) (n := n) ht' h
      have hne : v (t - t') ≠ v (z - t) := by
        intro heq
        exact hcons _ hmem ⟨heq ▸ hz1, heq ▸ hz2⟩
      have : z - t' = (z - t) + (t - t') := by ring
      rw [this]
      rcases lt_or_gt_of_ne hne with h1 | h1
      · rw [Valuation.map_add_eq_of_lt_left _ h1]; exact hzt.le
      · rw [Valuation.map_add_eq_of_lt_right _ h1]; exact h

variable [CompleteSpace K] [IsAlgClosed K]

theorem exists_good_ne_zero (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {g : ↥(affinoid ϖ n) → K} (hg : g ∈ holOn K (affinoid ϖ n)) (hg₀ : g ≠ 0)
    {t : K} (ht : t ∈ T₀) {e : K} (he0 : e ≠ 0) (he1 : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v e) (he2 : v e ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) :
    ∃ z : ↥(affinoid ϖ n), v ((z : K) - t) = v e ∧ (∀ t' ∈ T₀, v e ≤ v ((z : K) - t')) ∧ g z ≠ 0 := by
  obtain ⟨w, hwt, hwT⟩ := exists_generic_point t he0 T₀.val
  have hwT' : ∀ t' ∈ T₀, v e ≤ v (w - t') := fun t' ht' => hwT t' (Finset.mem_def.mp ht')
  have hwΩ : w ∈ affinoid ϖ n := good_mem hT ht he1 he2 hwt hwT'
  by_contra hall
  push Not at hall
  apply hg₀
  refine CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ hrk n hfin hg hwΩ he0
    fun z hz => ?_
  obtain ⟨hzt, hzT⟩ := good_of_near (A := T₀) hwt hwT' hz
  exact hall z hzt hzT

theorem finite_rim (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {g : ↥(affinoid ϖ n) → K} (hg : g ∈ holOn K (affinoid ϖ n)) (hg₀ : g ≠ 0)
    {t : K} (ht : t ∈ T₀) {e : K} (he0 : e ≠ 0) (he1 : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v e) (he2 : v e ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) :
    {z : ↥(affinoid ϖ n) | v ((z : K) - t) = v e ∧ (∀ t' ∈ T₀, v e ≤ v ((z : K) - t')) ∧ g z = 0}.Finite := by
  obtain ⟨s, hs0, Z, hZle, hZeq⟩ :=
    CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn K hg t e he0 T₀
      (fun z hz hzT => good_mem hT ht he1 he2 hz hzT) (exists_good_ne_zero hT hrk hfin hg hg₀ ht he0 he1 he2)

  set A : K → Set ↥(affinoid ϖ n) := fun ζ =>
    {z | (v ((z : K) - t) = v e ∧ (∀ t' ∈ T₀, v e ≤ v ((z : K) - t')) ∧ g z = 0) ∧ v ((z : K) - ζ) < v e} with hA
  have hAfin : ∀ ζ : K, (A ζ).Finite := by
    intro ζ
    rcases Set.eq_empty_or_nonempty (A ζ) with h0 | ⟨z₁, ⟨⟨hz₁t, hz₁T, -⟩, hz₁ζ⟩⟩
    · rw [h0]; exact Set.finite_empty

    have hout₀ : ∃ z : ↥(affinoid ϖ n), v ((z : K) - (z₁ : K)) = v e ∧
        (∀ t' ∈ T₀, v e ≤ v ((z : K) - t')) ∧ g z ≠ 0 := by
      obtain ⟨w, hwz, hwA⟩ := exists_generic_point (z₁ : K) he0 (T₀.val + Z.val)
      have hwT : ∀ t' ∈ T₀, v e ≤ v (w - t') := fun t' ht' =>
        hwA t' (Multiset.mem_add.2 (Or.inl (Finset.mem_def.mp ht')))
      have hwZ : ∀ ζ' ∈ Z, v e ≤ v (w - ζ') := fun ζ' hζ' =>
        hwA ζ' (Multiset.mem_add.2 (Or.inr (Finset.mem_def.mp hζ')))
      have hwt : v (w - t) = v e := by
        refine le_antisymm ?_ (hwT t ht)
        have : w - t = (w - z₁) + ((z₁ : K) - t) := by ring
        rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hwz.le hz₁t.le)
      have hwΩ : w ∈ affinoid ϖ n := good_mem hT ht he1 he2 hwt hwT
      refine ⟨⟨w, hwΩ⟩, hwz, hwT, fun h0 => hs0 ?_⟩
      have := hZeq ⟨w, hwΩ⟩ hwt hwT hwZ
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).1 this.symm
    have hfin' := CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn K hg (z₁ : K) e he0
      ∅ (fun _ => 1) (fun h hh => absurd hh (Finset.notMem_empty h)) (fun h hh => absurd hh (Finset.notMem_empty h))
      (fun h hh => absurd hh (Finset.notMem_empty h)) T₀
      (fun z hz _ => by
        obtain ⟨hzt, hzT⟩ := good_of_near (A := T₀) hz₁t hz₁T hz
        exact good_mem hT ht he1 he2 hzt hzT)
      (fun z hz hzT => by
        have hzt : v (z - t) = v e := by
          refine le_antisymm ?_ (hzT t ht)
          have : z - t = (z - z₁) + ((z₁ : K) - t) := by ring
          rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hz.le hz₁t.le)
        exact good_mem hT ht he1 he2 hzt hzT)
      (fun h hh => absurd hh (Finset.notMem_empty h)) hout₀ (fun h hh => absurd hh (Finset.notMem_empty h))
    refine hfin'.subset ?_
    rintro z ⟨⟨-, -, hz0⟩, hzζ⟩
    refine ⟨?_, fun h hh => absurd hh (Finset.notMem_empty h), hz0⟩
    have : (z : K) - z₁ = ((z : K) - ζ) - ((z₁ : K) - ζ) := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hzζ hz₁ζ)
  refine (Z.finite_toSet.biUnion fun ζ _ => hAfin ζ).subset ?_
  rintro z ⟨hzt, hzT, hz0⟩
  simp only [Set.mem_iUnion, Finset.mem_coe]
  by_contra hno
  push Not at hno
  have hZ' : ∀ ζ ∈ Z, v e ≤ v ((z : K) - ζ) := fun ζ hζ => by
    by_contra hlt
    exact hno ζ hζ ⟨⟨hzt, hzT, hz0⟩, lt_of_not_ge hlt⟩
  have := hZeq z hzt hzT hZ'
  rw [hz0, map_zero] at this
  exact hs0 ((Valuation.zero_iff _).1 this.symm)

theorem finite_region (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {g : ↥(affinoid ϖ n) → K} (hg : g ∈ holOn K (affinoid ϖ n)) (hg₀ : g ≠ 0)
    {t : K} (ht : t ∈ T₀) {eh el : K} (heh : eh ∈ crit ϖ n T₀ t) (hel : el ∈ crit ϖ n T₀ t) :
    {z : ↥(affinoid ϖ n) | v el < v ((z : K) - t) ∧ v ((z : K) - t) < v eh ∧
      (∀ e ∈ crit ϖ n T₀ t, ¬ (v el < v e ∧ v e < v eh)) ∧ g z = 0}.Finite := by
  by_cases hcons : ∀ e ∈ crit ϖ n T₀ t, ¬ (v el < v e ∧ v e < v eh)
  swap
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro z ⟨-, -, h, -⟩; exact hcons h
  obtain ⟨heh0, heh1, heh2⟩ := crit_bounds hT ht heh
  obtain ⟨hel0, hel1, hel2⟩ := crit_bounds hT ht hel
  have hfin' := CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn K hg t eh heh0
    {t} (fun _ => el) (fun _ _ => hel0)
    (fun h hh => by rw [Finset.mem_singleton.1 hh, sub_self, map_zero]; exact (Valuation.pos_iff _).2 heh0)
    (fun h hh h' hh' hne => absurd ((Finset.mem_singleton.1 hh).trans (Finset.mem_singleton.1 hh').symm) hne) T₀
    (fun z hz hzH => region_mem hT ht heh hel hcons (hzH t (Finset.mem_singleton_self t)) hz)
    (fun z hz hzT => good_mem hT ht heh1 heh2 hz hzT)
    (fun h hh z hz hzT => by
      rw [Finset.mem_singleton.1 hh] at hz
      exact good_mem hT ht hel1 hel2 hz hzT)
    (exists_good_ne_zero hT hrk hfin hg hg₀ ht heh0 heh1 heh2)
    (fun h hh => by
      rw [Finset.mem_singleton.1 hh]
      exact exists_good_ne_zero hT hrk hfin hg hg₀ ht hel0 hel1 hel2)
  refine hfin'.subset ?_
  rintro z ⟨hz1, hz2, -, hz0⟩
  exact ⟨hz2, fun h hh => by rw [Finset.mem_singleton.1 hh]; exact hz1, hz0⟩

theorem finite_zeros (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {g : ↥(affinoid ϖ n) → K} (hg : g ∈ holOn K (affinoid ϖ n)) (hg₀ : g ≠ 0)
    : {z : ↥(affinoid ϖ n) | g z = 0}.Finite := by

  have hbig : (⋃ t ∈ T₀, ((⋃ e ∈ crit ϖ n T₀ t,
      {z : ↥(affinoid ϖ n) | v ((z : K) - t) = v e ∧ (∀ t' ∈ T₀, v e ≤ v ((z : K) - t')) ∧ g z = 0}) ∪
      ⋃ eh ∈ crit ϖ n T₀ t, ⋃ el ∈ crit ϖ n T₀ t,
        {z : ↥(affinoid ϖ n) | v el < v ((z : K) - t) ∧ v ((z : K) - t) < v eh ∧
          (∀ e ∈ crit ϖ n T₀ t, ¬ (v el < v e ∧ v e < v eh)) ∧ g z = 0})).Finite := by
    refine T₀.finite_toSet.biUnion fun t ht => Set.Finite.union ?_ ?_
    · refine (crit ϖ n T₀ t).finite_toSet.biUnion fun e he => ?_
      obtain ⟨he0, he1, he2⟩ := crit_bounds hT ht he
      exact finite_rim hT hrk hfin hg hg₀ ht he0 he1 he2
    · refine (crit ϖ n T₀ t).finite_toSet.biUnion fun eh heh => (crit ϖ n T₀ t).finite_toSet.biUnion fun el hel => ?_
      exact finite_region hT hrk hfin hg hg₀ ht heh hel
  refine hbig.subset fun z hz0 => ?_
  have hz0 : g z = 0 := hz0
  obtain ⟨hzP, hzT⟩ := of_mem_affinoid hT z.2

  have hT₀ne : T₀.Nonempty := by
    obtain ⟨t, ht, -⟩ := hT.cover 0 (by rw [map_zero, map_zero]; exact zero_le')
    exact ⟨t, ht⟩
  obtain ⟨t, ht, hmin⟩ := T₀.exists_min_image (fun t => v ((z : K) - t)) hT₀ne
  simp only [Set.mem_iUnion, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq]
  refine ⟨t, ht, ?_⟩
  have hδ1 : (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ v ((z : K) - t) := hzT t ht
  have hδ2 : v ((z : K) - t) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := (Valuation.map_sub _ _ _).trans (max_le hzP (hT.size t ht))
  by_cases hA : ∃ e ∈ crit ϖ n T₀ t, v e = v ((z : K) - t)
  · obtain ⟨e, he, hev⟩ := hA
    exact Or.inl ⟨e, he, hev.symm, fun t' ht' => hev ▸ hmin t' ht', hz0⟩
  · push Not at hA

    have hupne : ((crit ϖ n T₀ t).filter fun e => v ((z : K) - t) < v e).Nonempty := by
      refine ⟨_, Finset.mem_filter.2 ⟨Pn_mem_crit (ϖ := ϖ) (n := n) t, lt_of_le_of_ne ?_ ?_⟩⟩
      · rw [v_Pn]; exact hδ2
      · exact fun h => hA _ (Pn_mem_crit t) h.symm
    have hlone : ((crit ϖ n T₀ t).filter fun e => v e < v ((z : K) - t)).Nonempty := by
      refine ⟨_, Finset.mem_filter.2 ⟨pn_mem_crit (ϖ := ϖ) (n := n) t, lt_of_le_of_ne ?_ ?_⟩⟩
      · rw [v_pn]; exact hδ1
      · exact hA _ (pn_mem_crit t)
    obtain ⟨eh, heh, hehmin⟩ := Finset.exists_min_image _ (fun e => v e) hupne
    obtain ⟨el, hel, helmax⟩ := Finset.exists_max_image _ (fun e => v e) hlone
    obtain ⟨hehc, hehz⟩ := Finset.mem_filter.1 heh
    obtain ⟨helc, helz⟩ := Finset.mem_filter.1 hel
    refine Or.inr ⟨eh, hehc, el, helc, helz, hehz, fun e he ⟨h1, h2⟩ => ?_, hz0⟩
    rcases lt_trichotomy (v e) (v ((z : K) - t)) with h | h | h
    · exact not_lt_of_ge (helmax e (Finset.mem_filter.2 ⟨he, h⟩)) h1
    · exact hA e he h
    · exact not_lt_of_ge (hehmin e (Finset.mem_filter.2 ⟨he, h⟩)) h2

end Aff

end P2mKcAffZeros

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : f ≠ 0) :
    Set.Finite {z : ↥(affinoid ϖ n) | f z = 0} := by
  classical
  obtain ⟨T₀, hT⟩ := P2mKcAffZeros.exists_centres (ϖ := ϖ) (n := n) hfin
  exact P2mKcAffZeros.finite_zeros hT hrk hfin hf hne

end
end S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid (solution)
