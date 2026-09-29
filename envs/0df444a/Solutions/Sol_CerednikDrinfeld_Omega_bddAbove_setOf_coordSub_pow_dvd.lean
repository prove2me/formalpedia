-- Prove2me | solution 1 for CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7d054ed7-8176-5618-8f8d-b5fd9876c8b3

import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd

set_option autoImplicit false

open Filter Polynomial
open scoped Topology
open CerednikDrinfeld.Omega

namespace P2mKcOrdFinite

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

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

theorem exists_circle_point_forall_v_evalAt_le [IsAlgClosed K] (p : RatPair K) (z₀ r : K) (hr : r ≠ 0)
    (hp : ∀ z : K, Valued.v (z - z₀) ≤ Valued.v r → p.den.eval z ≠ 0) :
    ∃ w₀ : K, Valued.v (w₀ - z₀) = Valued.v r ∧
      ∀ z : K, Valued.v (z - z₀) ≤ Valued.v r → Valued.v (p.evalAt z) ≤ Valued.v (p.evalAt w₀) := by
  classical
  have hvr : Valued.v r ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hvr0 : 0 < Valued.v r := zero_lt_iff.2 hvr

  set R : Multiset K := p.num.roots + p.den.roots with hR
  set T : Multiset K := (R.filter fun α => Valued.v (α - z₀) ≤ Valued.v r).map fun α => (α - z₀) / r with hT
  have hT1 : ∀ b ∈ T, Valued.v b ≤ 1 := by
    intro b hb
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb
    have hα' := (Multiset.mem_filter.1 hα).2
    rw [map_div₀, div_le_one₀ hvr0]
    exact hα'
  obtain ⟨u, hu1, hu⟩ := exists_generic_unit T hT1
  set w₀ : K := z₀ + r * u with hw₀
  have hw₀z : w₀ - z₀ = r * u := by rw [hw₀]; ring
  have hvw₀ : Valued.v (w₀ - z₀) = Valued.v r := by rw [hw₀z, map_mul, hu1, mul_one]
  refine ⟨w₀, hvw₀, fun z hz => ?_⟩

  have hfac : ∀ α ∈ R, Valued.v (z - α) ≤ Valued.v (w₀ - α) ∧
      (Valued.v r < Valued.v (α - z₀) → Valued.v (z - α) = Valued.v (w₀ - α)) := by
    intro α hα
    by_cases hclose : Valued.v (α - z₀) ≤ Valued.v r
    ·
      have hb : (α - z₀) / r ∈ T := Multiset.mem_map_of_mem _ (Multiset.mem_filter.2 ⟨hα, hclose⟩)
      have hw : Valued.v (w₀ - α) = Valued.v r := by
        have : w₀ - α = r * (u - (α - z₀) / r) := by rw [hw₀, mul_sub, mul_div_cancel₀ _ hr]; ring
        rw [this, map_mul, hu _ hb, mul_one]
      refine ⟨?_, fun hfar => absurd hclose (not_le.2 hfar)⟩
      rw [hw]
      have : z - α = (z - z₀) - (α - z₀) := by ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans (max_le hz hclose)
    · push Not at hclose
      have hw : Valued.v (w₀ - α) = Valued.v (α - z₀) := by
        have : w₀ - α = (w₀ - z₀) - (α - z₀) := by ring
        rw [this]
        exact Valuation.map_sub_eq_of_lt_right _ (hvw₀ ▸ hclose)
      have hzα : Valued.v (z - α) = Valued.v (α - z₀) := by
        have : z - α = (z - z₀) - (α - z₀) := by ring
        rw [this]
        exact Valuation.map_sub_eq_of_lt_right _ (hz.trans_lt hclose)
      exact ⟨by rw [hw, hzα], fun _ => by rw [hw, hzα]⟩

  have hnum : Valued.v (p.num.eval z) ≤ Valued.v (p.num.eval w₀) := by
    rw [(IsAlgClosed.splits p.num).eval_eq_prod_roots z, (IsAlgClosed.splits p.num).eval_eq_prod_roots w₀,
      map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    refine mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ fun α hα => ?_) _
    exact (hfac α (by rw [hR]; exact Multiset.mem_add.2 (Or.inl hα))).1

  have hden : Valued.v (p.den.eval z) = Valued.v (p.den.eval w₀) := by
    rw [(IsAlgClosed.splits p.den).eval_eq_prod_roots z, (IsAlgClosed.splits p.den).eval_eq_prod_roots w₀,
      map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β hβ => ?_)
    have hβroot : p.den.eval β = 0 := by
      have hne : p.den ≠ 0 := fun h0 => by
        have := hp z₀ (by simp); rw [h0, eval_zero] at this; exact this rfl
      exact (mem_roots hne).1 hβ
    have hfar : Valued.v r < Valued.v (β - z₀) := by
      by_contra hle
      push Not at hle
      exact hp β hle hβroot
    exact (hfac β (by rw [hR]; exact Multiset.mem_add.2 (Or.inr hβ))).2 hfar
  have hw₀D : Valued.v (w₀ - z₀) ≤ Valued.v r := hvw₀.le
  have hQw : Valued.v (p.den.eval w₀) ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hp w₀ hw₀D
  rw [RatPair.evalAt, RatPair.evalAt, map_div₀, map_div₀, hden]
  exact div_le_div_of_nonneg_right hnum zero_le'

theorem v_le_of_forall_circle [IsAlgClosed K] {S : Set K} {q : ↥S → K} (hq : q ∈ holOn K S)
    {z₀ r : K} (hr : r ≠ 0) (hD : ∀ w : K, Valued.v (w - z₀) ≤ Valued.v r → w ∈ S)
    (M : Γ₀) (hM : ∀ w : ↥S, Valued.v ((w : K) - z₀) = Valued.v r → Valued.v (q w) ≤ M)
    (w : ↥S) (hw : Valued.v ((w : K) - z₀) ≤ Valued.v r) : Valued.v (q w) ≤ M := by
  by_contra hlt
  push Not at hlt
  have hqw : q w ≠ 0 := fun h => by
    rw [h, map_zero] at hlt
    exact not_le.2 hlt zero_le'
  obtain ⟨s, hs, -, hlim⟩ := hq
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have hunit : vRestrict K (q w) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hunit))
  have hk' : ∀ y : ↥S, Valued.v ((s k).evalAt y - q y) < Valued.v (q w) := fun y => by
    rw [v_lt_iff_vRestrict_lt]
    exact hk k le_rfl y
  obtain ⟨w₀, hw₀, hmax⟩ :=
    exists_circle_point_forall_v_evalAt_le (s k) z₀ r hr (fun y hy => hs k y (hD y hy))
  have hw₀S : w₀ ∈ S := hD w₀ hw₀.le
  have h1 : Valued.v ((s k).evalAt w) = Valued.v (q w) := by
    have : (s k).evalAt w = q w + ((s k).evalAt w - q w) := by ring
    rw [this]
    exact Valuation.map_add_eq_of_lt_left _ (hk' w)
  have h2 : Valued.v ((s k).evalAt w₀) < Valued.v (q w) := by
    have : (s k).evalAt w₀ = q ⟨w₀, hw₀S⟩ + ((s k).evalAt w₀ - q ⟨w₀, hw₀S⟩) := by ring
    rw [this]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ (hk' ⟨w₀, hw₀S⟩))
    exact lt_of_le_of_lt (hM ⟨w₀, hw₀S⟩ hw₀) hlt
  have h3 := hmax w hw
  rw [h1] at h3
  exact absurd (lt_of_le_of_lt h3 h2) (lt_irrefl _)

section Omega

variable {K₀ : Type} [Field K₀] [Algebra K₀ K] (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem pow_succ_lt_pow (n : ℕ) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos ϖ.pos n) ϖ.lt_one

theorem mem_affinoid_of_v_sub_le {n : ℕ} {z : K} (hz : z ∈ affinoid ϖ n) {w : K}
    (hw : Valued.v (w - z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) : w ∈ affinoid ϖ n := by
  have hp0 : 0 < Valued.v (algebraMap K₀ K ϖ.ϖ) := ϖ.pos
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  rw [mem_affinoid_iff'] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  have hwz : Valued.v (w - z) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := lt_of_le_of_lt hw (pow_succ_lt_pow ϖ n)
  constructor
  · have h1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ 1 := pow_le_one₀ zero_le' hp1.le
    have h2 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1.le)
    have : w = (w - z) + z := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (hwz.le.trans (h1.trans h2)) hz1)
  · intro a
    have hza := hz2 a
    have hlt' : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K a) := lt_of_lt_of_le hwz hza
    have : w - algebraMap K₀ K a = (w - z) + (z - algebraMap K₀ K a) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ hlt']
    exact hza

theorem coe_mul_apply (F G : ↥(holRing ϖ)) (w : ↥(upperHalfPlane K₀ K)) :
    ((F * G : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      (F : ↥(upperHalfPlane K₀ K) → K) w * (G : ↥(upperHalfPlane K₀ K) → K) w := rfl

theorem coe_pow_apply (F : ↥(holRing ϖ)) (n : ℕ) (w : ↥(upperHalfPlane K₀ K)) :
    ((F ^ n : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w = ((F : ↥(upperHalfPlane K₀ K) → K) w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, coe_mul_apply, ih, pow_succ]

theorem coordSub_pow_mul_apply (z : ↥(upperHalfPlane K₀ K)) (n : ℕ) (Q : ↥(holRing ϖ))
    (w : ↥(upperHalfPlane K₀ K)) :
    ((coordSub ϖ z ^ n * Q : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      ((w : K) - z) ^ n * (Q : ↥(upperHalfPlane K₀ K) → K) w := by
  rw [coe_mul_apply, coe_pow_apply, coordSub_apply]

theorem bddAbove_setOf_pow_dvd [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(holRing ϖ)) (hF : F ≠ 0) (z : ↥(upperHalfPlane K₀ K)) :
    BddAbove {n : ℕ | coordSub ϖ z ^ n ∣ F} := by
  by_contra hnb
  apply hF
  have hall : ∀ m : ℕ, coordSub ϖ z ^ m ∣ F := by
    intro m
    obtain ⟨n, hn, hmn⟩ := not_bddAbove_iff.1 hnb m
    exact (pow_dvd_pow _ hmn.le).trans hn
  obtain ⟨N, hzN⟩ := hex z z.2
  set r : K := algebraMap K₀ K ϖ.ϖ ^ (N + 1) with hrdef
  have hr : r ≠ 0 := pow_ne_zero _ (algebraMap_varpi_ne_zero ϖ)
  have hvr : Valued.v r = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (N + 1) := map_pow _ _ _
  have hvr0 : 0 < Valued.v r := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
  have hD : ∀ w : K, Valued.v (w - z) ≤ Valued.v r → w ∈ affinoid ϖ N := fun w hw =>
    mem_affinoid_of_v_sub_le ϖ hzN (hvr ▸ hw)
  obtain ⟨B, hB⟩ := (F.2 N).bounded

  have hzero : ∀ w : ↥(affinoid ϖ N), Valued.v ((w : K) - z) < Valued.v r →
      (F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ N w.2⟩ = 0 := by
    intro w hw
    by_cases hwz : (w : K) = z
    · obtain ⟨Q, hQ⟩ := hall 1
      have h1 : (F : ↥(upperHalfPlane K₀ K) → K) z = ((z : K) - z) ^ 1 * (Q : ↥(upperHalfPlane K₀ K) → K) z := by
        rw [hQ]; exact coordSub_pow_mul_apply ϖ z 1 Q z
      rw [sub_self, pow_one, zero_mul] at h1
      have hwz' : (⟨(w : K), affinoid_subset_upperHalfPlane ϖ N w.2⟩ : ↥(upperHalfPlane K₀ K)) = z :=
        Subtype.ext hwz
      rw [hwz']
      exact h1
    · by_contra hFw

      have hest : ∀ m : ℕ, Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ N w.2⟩) ≤
          (Valued.v ((w : K) - z) / Valued.v r) ^ m * Valued.v B := by
        intro m
        obtain ⟨Q, hQ⟩ := hall m
        have hFQ : ∀ y : ↥(affinoid ϖ N), (F : ↥(upperHalfPlane K₀ K) → K) ⟨y, affinoid_subset_upperHalfPlane ϖ N y.2⟩ =
            ((y : K) - z) ^ m * restrictAffinoid ϖ N Q y := fun y => by
          rw [hQ]; exact coordSub_pow_mul_apply ϖ z m Q _

        have hcirc : ∀ y : ↥(affinoid ϖ N), Valued.v ((y : K) - z) = Valued.v r →
            Valued.v (restrictAffinoid ϖ N Q y) ≤ Valued.v B / Valued.v r ^ m := by
          intro y hy
          have hyz : Valued.v ((y : K) - z) ^ m ≠ 0 := by rw [hy]; exact pow_ne_zero _ hvr0.ne'
          rw [le_div_iff₀ (pow_pos hvr0 m), ← hy]
          calc Valued.v (restrictAffinoid ϖ N Q y) * Valued.v ((y : K) - z) ^ m
              = Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨y, affinoid_subset_upperHalfPlane ϖ N y.2⟩) := by
                rw [hFQ y, map_mul, map_pow, mul_comm]
            _ ≤ Valued.v B := hB y
        have hQw : Valued.v (restrictAffinoid ϖ N Q w) ≤ Valued.v B / Valued.v r ^ m :=
          v_le_of_forall_circle (Q.2 N) hr hD _ hcirc w hw.le
        calc Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ N w.2⟩)
            = Valued.v ((w : K) - z) ^ m * Valued.v (restrictAffinoid ϖ N Q w) := by
              rw [hFQ w, map_mul, map_pow]
          _ ≤ Valued.v ((w : K) - z) ^ m * (Valued.v B / Valued.v r ^ m) := mul_le_mul_right hQw _
          _ = (Valued.v ((w : K) - z) / Valued.v r) ^ m * Valued.v B := by
              rw [div_pow, div_mul_eq_mul_div, ← mul_div_assoc]

      set Fw := (F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane ϖ N w.2⟩ with hFwdef
      have hvFw : 0 < Valued.v Fw := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
      have hvB : 0 < Valued.v B := lt_of_lt_of_le hvFw (hB w)
      have hB0 : B ≠ 0 := fun h => by rw [h, map_zero] at hvB; exact lt_irrefl _ hvB
      set x : K := ((w : K) - z) / r with hxdef
      have hx0 : x ≠ 0 := div_ne_zero (sub_ne_zero.2 hwz) hr
      have hvx : Valued.v x = Valued.v ((w : K) - z) / Valued.v r := map_div₀ _ _ _
      have hvx1 : Valued.v x < 1 := by rw [hvx, div_lt_one₀ hvr0]; exact hw
      have hvx0 : 0 < Valued.v x := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
      obtain ⟨n, hn⟩ := hrk x (Fw / B * x) hvx1 (mul_ne_zero (div_ne_zero hFw hB0) hx0)
      have h1 : Valued.v x ^ n < Valued.v Fw / Valued.v B := by
        refine lt_of_le_of_lt hn ?_
        rw [map_mul, map_div₀]
        exact mul_lt_of_lt_one_right (div_pos hvFw hvB) hvx1
      have h2 : Valued.v x ^ n * Valued.v B < Valued.v Fw := by
        rwa [lt_div_iff₀ hvB] at h1
      have h3 := hest n
      rw [← hvx] at h3
      exact absurd (lt_of_le_of_lt h3 h2) (lt_irrefl _)

  have hlevel : ∀ n : ℕ, N ≤ n → restrictAffinoid ϖ n F = 0 := by
    intro n hn
    have hzn : (z : K) ∈ affinoid ϖ n := affinoid_mono ϖ hn hzN
    refine CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ hrk n
      (hfin n) (F.2 n) hzn hr fun w hw => ?_
    have hwN : (w : K) ∈ affinoid ϖ N := hD w hw.le
    exact hzero ⟨w, hwN⟩ hw

  refine Subtype.ext (funext fun w => ?_)
  obtain ⟨k, hk⟩ := hex w w.2
  have hwn : (w : K) ∈ affinoid ϖ (max k N) := affinoid_mono ϖ (le_max_left k N) hk
  have := congrFun (hlevel (max k N) (le_max_right k N)) ⟨w, hwn⟩
  exact this

end Omega

end P2mKcOrdFinite

open scoped MatrixGroups in
open CerednikDrinfeld CerednikDrinfeld.Omega P2mKcOrdFinite in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)

    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (F : ↥(Omega.holRing ϖ)) (hF : F ≠ 0) (z : ↥(Omega.upperHalfPlane K₀ K)) :
    BddAbove {n : ℕ | Omega.coordSub ϖ z ^ n ∣ F} :=
  bddAbove_setOf_pow_dvd ϖ hrk hex hfin F hF z

end S_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd (solution)
