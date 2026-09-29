-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7f7f370a-3784-5348-84c6-6654034351c6

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid

set_option autoImplicit false

p2m_open "Polynomial CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid mem_affinoid_iff' holOn mem_holOn_iff exists_mem_holOn_eq_sub_mul_of_apply_eq_zero eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset"
namespace OrdFinAtAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

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

end Omega

end CerednikDrinfeld.Omega.OrdFinAtAux

open CerednikDrinfeld.Omega.OrdFinAtAux in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : ∃ z : ↥(affinoid ϖ n), f z ≠ 0)
    (p : ↥(affinoid ϖ n)) :
    ∃ (k : ℕ) (g : ↥(affinoid ϖ n) → K), g ∈ holOn K (affinoid ϖ n) ∧ g p ≠ 0 ∧
      ∀ z : ↥(affinoid ϖ n), f z = ((z : K) - (p : K)) ^ k * g z := by
  classical

  set r : K := algebraMap K₀ K ϖ.ϖ ^ (n + 1) with hrdef
  have hr : r ≠ 0 := pow_ne_zero _ (algebraMap_varpi_ne_zero ϖ)
  have hvr : Valued.v r = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) := map_pow _ _ _
  have hvr0 : 0 < Valued.v r := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
  have hD : ∀ w : K, Valued.v (w - (p : K)) ≤ Valued.v r → w ∈ affinoid ϖ n := fun w hw =>
    mem_affinoid_of_v_sub_le ϖ p.2 (hvr ▸ hw)
  by_contra hcon

  have hall : ∀ k : ℕ, ∃ g : ↥(affinoid ϖ n) → K, g ∈ holOn K (affinoid ϖ n) ∧
      ∀ z : ↥(affinoid ϖ n), f z = ((z : K) - (p : K)) ^ k * g z := by
    intro k
    induction k with
    | zero => exact ⟨f, hf, fun z => by rw [pow_zero, one_mul]⟩
    | succ k ih =>
      obtain ⟨g, hg, hfg⟩ := ih
      have hgp : g p = 0 := by
        by_contra hgp
        exact hcon ⟨k, g, hg, hgp, hfg⟩
      obtain ⟨g', hg', hgg'⟩ :=
        CerednikDrinfeld.Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero K hg p hgp r hr hD
      refine ⟨g', hg', fun z => ?_⟩
      rw [hfg z, hgg' z, pow_succ, mul_assoc]
  obtain ⟨B, hB⟩ := ((mem_holOn_iff f).1 hf).bounded

  have hzero : ∀ w : ↥(affinoid ϖ n), Valued.v ((w : K) - (p : K)) < Valued.v r → f w = 0 := by
    intro w hw
    by_cases hwp : (w : K) = (p : K)
    · obtain ⟨g, -, hfg⟩ := hall 1
      have hw' : w = p := Subtype.ext hwp
      rw [hfg w, hw', sub_self, pow_one, zero_mul]
    · by_contra hfw

      have hest : ∀ m : ℕ, Valued.v (f w) ≤ (Valued.v ((w : K) - (p : K)) / Valued.v r) ^ m * Valued.v B := by
        intro m
        obtain ⟨g, hg, hfg⟩ := hall m

        have hcirc : ∀ y : ↥(affinoid ϖ n), Valued.v ((y : K) - (p : K)) = Valued.v r →
            Valued.v (g y) ≤ Valued.v B / Valued.v r ^ m := by
          intro y hy
          rw [le_div_iff₀ (pow_pos hvr0 m), ← hy]
          calc Valued.v (g y) * Valued.v ((y : K) - (p : K)) ^ m = Valued.v (f y) := by
                rw [hfg y, map_mul, map_pow, mul_comm]
            _ ≤ Valued.v B := hB y

        have hgw : Valued.v (g w) ≤ Valued.v B / Valued.v r ^ m := by
          obtain ⟨E, hE⟩ :=
            CerednikDrinfeld.Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
              K (affinoid ϖ n) (p : K) r hr hD hg
          obtain ⟨z₀, hz₀, hgen⟩ := exists_generic_point (K := K) (p : K) hr E.val
          have hgen' : ∀ e ∈ E, Valued.v r ≤ Valued.v (z₀ - e) := fun e he => hgen e (Finset.mem_val.mpr he)
          have h1 := hE z₀ hz₀ hgen' (w : K) hw.le
          exact h1.trans (hcirc ⟨z₀, hD z₀ hz₀.le⟩ hz₀)
        calc Valued.v (f w) = Valued.v ((w : K) - (p : K)) ^ m * Valued.v (g w) := by
              rw [hfg w, map_mul, map_pow]
          _ ≤ Valued.v ((w : K) - (p : K)) ^ m * (Valued.v B / Valued.v r ^ m) := mul_le_mul_right hgw _
          _ = (Valued.v ((w : K) - (p : K)) / Valued.v r) ^ m * Valued.v B := by
              rw [div_pow, div_mul_eq_mul_div, ← mul_div_assoc]

      have hvFw : 0 < Valued.v (f w) := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])
      have hvB : 0 < Valued.v B := lt_of_lt_of_le hvFw (hB w)
      have hB0 : B ≠ 0 := fun h => by rw [h, map_zero] at hvB; exact lt_irrefl _ hvB
      set x : K := ((w : K) - (p : K)) / r with hxdef
      have hx0 : x ≠ 0 := div_ne_zero (sub_ne_zero.2 hwp) hr
      have hvx : Valued.v x = Valued.v ((w : K) - (p : K)) / Valued.v r := map_div₀ _ _ _
      have hvx1 : Valued.v x < 1 := by rw [hvx, div_lt_one₀ hvr0]; exact hw
      obtain ⟨N, hN⟩ := hrk x (f w / B * x) hvx1 (mul_ne_zero (div_ne_zero hfw hB0) hx0)
      have h1 : Valued.v x ^ N < Valued.v (f w) / Valued.v B := by
        refine lt_of_le_of_lt hN ?_
        rw [map_mul, map_div₀]
        exact mul_lt_of_lt_one_right (div_pos hvFw hvB) hvx1
      have h2 : Valued.v x ^ N * Valued.v B < Valued.v (f w) := by
        rwa [lt_div_iff₀ hvB] at h1
      have h3 := hest N
      rw [← hvx] at h3
      exact absurd (lt_of_le_of_lt h3 h2) (lt_irrefl _)

  have hf0 : f = 0 :=
    CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ hrk n hfin hf
      p.2 hr (fun z hz => hzero z hz)
  obtain ⟨z, hz⟩ := hne
  exact hz (by rw [hf0]; rfl)

end S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_eq_sub_pow_mul_and_apply_ne_zero_of_mem_holOn_affinoid (solution)
