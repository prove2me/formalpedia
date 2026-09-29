-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f1b13f0d-a838-5ef5-b77d-86e4c342ccf3

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Filter
open CerednikDrinfeld.Omega

namespace P2mKcGenericModulus

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def gauss (P : K[X]) : Γ₀ := P.support.sup fun i => Valued.v (P.coeff i)

theorem v_coeff_le_gauss (P : K[X]) (i : ℕ) : v (P.coeff i) ≤ gauss P := by
  by_cases h : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)) h
  · rw [Polynomial.notMem_support_iff.1 h, map_zero]; exact zero_le'

theorem gauss_le {P : K[X]} {γ : Γ₀} (h : ∀ i, v (P.coeff i) ≤ γ) : gauss P ≤ γ :=
  Finset.sup_le fun i _ => h i

theorem gauss_zero : gauss (0 : K[X]) = 0 := by simp [gauss, bot_eq_zero]

theorem exists_eq_gauss {P : K[X]} (hP : P ≠ 0) : ∃ i ∈ P.support, v (P.coeff i) = gauss P := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun i => v (P.coeff i))
  exact ⟨i, hi, h.symm⟩

theorem gauss_pos {P : K[X]} (hP : P ≠ 0) : 0 < gauss P := by
  obtain ⟨i, hi, h⟩ := exists_eq_gauss hP
  rw [← h, Valuation.pos_iff]
  exact Polynomial.mem_support_iff.1 hi

theorem gauss_ne_zero {P : K[X]} (hP : P ≠ 0) : gauss P ≠ 0 := (gauss_pos hP).ne'

theorem gauss_C (a : K) : gauss (C a : K[X]) = v a := by
  apply le_antisymm
  · exact gauss_le fun i => by
      rw [coeff_C]; split_ifs
      · exact le_rfl
      · rw [map_zero]; exact zero_le'
  · simpa using v_coeff_le_gauss (C a) 0

theorem v_eval_le_gauss (P : K[X]) {y : K} (hy : v y ≤ 1) : v (P.eval y) ≤ gauss P := by
  rw [eval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, map_pow]
  exact (mul_le_mul' le_rfl (pow_le_one₀ zero_le' hy)).trans (by rw [mul_one]; exact v_coeff_le_gauss P i)

theorem gauss_mul_X_sub_C (P : K[X]) (α : K) : gauss (P * (X - C α)) = gauss P * max 1 (v α) := by
  by_cases hP : P = 0
  · rw [hP, zero_mul, gauss_zero, zero_mul]
  have hc0 : (P * (X - C α)).coeff 0 = -(P.coeff 0 * α) := by
    rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]
  have hcs : ∀ a : ℕ, (P * (X - C α)).coeff (a + 1) = P.coeff a - P.coeff (a + 1) * α := fun a =>
    coeff_mul_X_sub_C
  apply le_antisymm
  · refine gauss_le fun i => ?_
    rcases i with _ | a
    · rw [hc0, Valuation.map_neg, map_mul]
      exact mul_le_mul' (v_coeff_le_gauss P 0) (le_max_right _ _)
    · rw [hcs]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · calc v (P.coeff a) = v (P.coeff a) * 1 := (mul_one _).symm
          _ ≤ gauss P * max 1 (v α) := mul_le_mul' (v_coeff_le_gauss P a) (le_max_left _ _)
      · rw [map_mul]; exact mul_le_mul' (v_coeff_le_gauss P _) (le_max_right _ _)
  · classical
    let I : Finset ℕ := P.support.filter fun i => v (P.coeff i) = gauss P
    have hI : I.Nonempty := by
      obtain ⟨i, hi, h⟩ := exists_eq_gauss hP
      exact ⟨i, Finset.mem_filter.2 ⟨hi, h⟩⟩
    have hIspec : ∀ i ∈ I, v (P.coeff i) = gauss P := fun i hi => (Finset.mem_filter.1 hi).2
    have hlt_of_notMem : ∀ i, i ∉ I → v (P.coeff i) < gauss P := fun i hi => by
      refine lt_of_le_of_ne (v_coeff_le_gauss P i) fun h => hi ?_
      refine Finset.mem_filter.2 ⟨Polynomial.mem_support_iff.2 fun h0 => ?_, h⟩
      rw [h0, map_zero] at h; exact gauss_ne_zero hP h.symm
    rcases le_or_gt (v α) 1 with hα | hα
    · rw [max_eq_left hα, mul_one]
      set j := I.max' hI with hj
      have hjI : j ∈ I := Finset.max'_mem I hI
      have hj1 : v (P.coeff (j + 1)) < gauss P := hlt_of_notMem _ fun h =>
        absurd (Finset.le_max' I _ h) (by rw [← hj]; omega)
      have hlt : v (P.coeff (j + 1) * α) < v (P.coeff j) := by
        rw [map_mul, hIspec j hjI]
        exact lt_of_le_of_lt (mul_le_mul' le_rfl hα) (by rw [mul_one]; exact hj1)
      calc gauss P = v ((P * (X - C α)).coeff (j + 1)) := by
            rw [hcs, Valuation.map_sub_eq_of_lt_left _ hlt, hIspec j hjI]
        _ ≤ gauss (P * (X - C α)) := v_coeff_le_gauss _ _
    · rw [max_eq_right hα.le]
      have key : ∀ j, j = I.min' hI → v ((P * (X - C α)).coeff j) = gauss P * v α := by
        intro j hj
        have hjI : j ∈ I := hj ▸ Finset.min'_mem I hI
        rcases j with _ | a
        · rw [hc0, Valuation.map_neg, map_mul, hIspec _ hjI]
        · have ha : v (P.coeff a) < gauss P := hlt_of_notMem _ fun h =>
            absurd (Finset.min'_le I _ h) (by rw [← hj]; omega)
          have hlt : v (P.coeff a) < v (P.coeff (a + 1) * α) := by
            rw [map_mul, hIspec _ hjI]
            exact lt_of_lt_of_le ha (le_of_lt (lt_of_le_of_lt (mul_one _).symm.le
              (mul_lt_mul_of_pos_left hα (gauss_pos hP))))
          rw [hcs, Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, hIspec _ hjI]
      calc gauss P * v α = v ((P * (X - C α)).coeff (I.min' hI)) := (key _ rfl).symm
        _ ≤ gauss (P * (X - C α)) := v_coeff_le_gauss _ _

theorem gauss_mul_prod_X_sub_C (P : K[X]) (s : Multiset K) :
    gauss (P * (s.map fun α => X - C α).prod) = gauss P * (s.map fun α => max 1 (v α)).prod := by
  induction s using Multiset.induction_on generalizing P with
  | empty => simp
  | cons α s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc, ih, gauss_mul_X_sub_C, Multiset.map_cons,
      Multiset.prod_cons, mul_assoc]

section AlgClosed

variable [IsAlgClosed K]

theorem eq_C_mul_prod (P : K[X]) : P = C P.leadingCoeff * (P.roots.map fun α => X - C α).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((splits_iff_card_roots.1 (IsAlgClosed.splits P)).symm ▸ rfl)).symm

theorem gauss_eq_prod_roots (P : K[X]) :
    gauss P = v P.leadingCoeff * (P.roots.map fun α => max 1 (v α)).prod := by
  conv_lhs => rw [eq_C_mul_prod P]
  rw [gauss_mul_prod_X_sub_C, gauss_C]

theorem v_eval_eq_gauss (P : K[X]) {y : K} (hy : v y ≤ 1)
    (hgen : ∀ α ∈ P.roots, v α ≤ 1 → 1 ≤ v (y - α)) : v (P.eval y) = gauss P := by
  conv_lhs => rw [eq_C_mul_prod P]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod, Multiset.map_map,
    gauss_eq_prod_roots]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => ?_)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  rcases le_or_gt (v α) 1 with h | h
  · rw [max_eq_left h]
    exact le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hy h)) (hgen α hα h)
  · rw [max_eq_right h.le]
    exact Valuation.map_sub_eq_of_lt_right _ (hy.trans_lt h)

end AlgClosed

def scl (c R : K) (P : K[X]) : K[X] := P.comp (C c + C R * X)

theorem eval_scl (c R : K) (P : K[X]) (y : K) : (scl c R P).eval y = P.eval (c + R * y) := by
  simp [scl, eval_comp]

theorem eval_scl_hat (c : K) {R : K} (hR : R ≠ 0) (P : K[X]) (z : K) :
    (scl c R P).eval ((z - c) / R) = P.eval z := by
  rw [eval_scl, mul_div_cancel₀ _ hR, add_sub_cancel]

theorem v_hat (c : K) {R : K} (hR : R ≠ 0) (z : K) : v ((z - c) / R) = v (z - c) / v R := map_div₀ _ _ _

theorem v_hat_eq_one (c : K) {R : K} (hR : R ≠ 0) {z : K} (hz : v (z - c) = v R) : v ((z - c) / R) = 1 := by
  rw [v_hat c hR, hz, div_self ((Valuation.ne_zero_iff _).2 hR)]

theorem hat_sub_hat (c : K) {R : K} (hR : R ≠ 0) (z w : K) : (z - c) / R - (w - c) / R = (z - w) / R := by
  field_simp; ring

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

theorem unif_eps {α : Type} {F : ℕ → α → K} {φ : α → K} (h : TendstoUniformly F φ atTop) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z, v (F k z - φ z) < v e := fun e he => by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hwe : vRestrict K e ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (Units.mk0 _ hwe))
  exact ⟨N, fun k hk z => (v_lt_iff_vRestrict_lt K _ _).2 (hN k hk z)⟩

theorem good_of_near {c R : K} (hR : R ≠ 0) {E : Finset K} {z w : K}
    (hz : v (z - c) = v R) (hzE : ∀ e ∈ E, v R ≤ v (z - e)) (hw : v (w - z) < v R) :
    v (w - c) = v R ∧ ∀ e ∈ E, v R ≤ v (w - e) := by
  constructor
  · have : w - c = (w - z) + (z - c) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rw [hz]; exact hw), hz]
  · intro e he
    have : w - e = (w - z) + (z - e) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (hw.trans_le (hzE e he))]
    exact hzE e he

theorem main [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0) (E : Finset K)
    (hS : ∀ z : K, v (z - c) = v R → (∀ e ∈ E, v R ≤ v (z - e)) → z ∈ S)
    (h₀ : ∃ z : ↥S, v ((z : K) - c) = v R ∧ (∀ e ∈ E, v R ≤ v ((z : K) - e)) ∧ f z ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ Z : Finset K,
      (∀ z : ↥S, v ((z : K) - c) = v R → (∀ e ∈ E, v R ≤ v ((z : K) - e)) → v (f z) ≤ v s) ∧
      (∀ z : ↥S, v ((z : K) - c) = v R → (∀ e ∈ E, v R ≤ v ((z : K) - e)) →
        (∀ ζ ∈ Z, v R ≤ v ((z : K) - ζ)) → v (f z) = v s) := by
  classical
  obtain ⟨z₀, hz₀c, hz₀E, hfz₀⟩ := h₀
  obtain ⟨r, hpf, -, hlim⟩ := hf
  have hvR : v R ≠ 0 := (Valuation.ne_zero_iff _).2 hR
  have hvRpos : 0 < v R := zero_lt_iff.2 hvR

  obtain ⟨N, hN⟩ := unif_eps hlim (f z₀) hfz₀
  set p : K[X] := (r N).num with hp
  set q : K[X] := (r N).den with hq
  have hclose : ∀ z : ↥S, v ((r N).evalAt z - f z) < v (f z₀) := fun z => hN N le_rfl z
  have hqz : ∀ z : ↥S, q.eval (z : K) ≠ 0 := fun z => hpf N z z.2
  have hev : ∀ z : ↥S, (r N).evalAt z = p.eval (z : K) / q.eval (z : K) := fun z => rfl

  set ph : K[X] := scl c R p with hph
  set qh : K[X] := scl c R q with hqh
  have hph_ev : ∀ z : K, ph.eval ((z - c) / R) = p.eval z := fun z => eval_scl_hat c hR p z
  have hqh_ev : ∀ z : K, qh.eval ((z - c) / R) = q.eval z := fun z => eval_scl_hat c hR q z

  have hq_gen : ∀ z : K, v (z - c) = v R → (∀ e ∈ E, v R ≤ v (z - e)) →
      ∀ β ∈ qh.roots, v β ≤ 1 → 1 ≤ v ((z - c) / R - β) := by
    intro z hz hzE β hβ hβ1
    by_contra hlt
    push Not at hlt

    set w : K := c + R * β with hw
    have hwβ : (w - c) / R = β := by rw [hw]; field_simp; ring
    have hwz : v (w - z) < v R := by
      have : w - z = -(R * ((z - c) / R - β)) := by rw [hw]; field_simp; ring
      rw [this, Valuation.map_neg, map_mul]
      calc v R * v ((z - c) / R - β) < v R * 1 := mul_lt_mul_of_pos_left hlt hvRpos
        _ = v R := mul_one _
    obtain ⟨hwc, hwE⟩ := good_of_near hR hz hzE hwz
    have hwS : w ∈ S := hS w hwc hwE
    have hq0 : q.eval w = 0 := by
      have := (mem_roots'.1 hβ).2
      rw [IsRoot.def] at this
      rw [← hqh_ev w, hwβ]; exact this
    exact hqz ⟨w, hwS⟩ hq0

  have hvq : ∀ z : K, v (z - c) = v R → (∀ e ∈ E, v R ≤ v (z - e)) → v (q.eval z) = gauss qh := by
    intro z hz hzE
    rw [← hqh_ev z]
    exact v_eval_eq_gauss qh (v_hat_eq_one c hR hz).le (hq_gen z hz hzE)

  have hvp_le : ∀ z : K, v (z - c) = v R → v (p.eval z) ≤ gauss ph := by
    intro z hz
    rw [← hph_ev z]
    exact v_eval_le_gauss ph (v_hat_eq_one c hR hz).le
  set Z : Finset K := (ph.roots.map fun β => c + R * β).toFinset with hZ
  have hvp_eq : ∀ z : K, v (z - c) = v R → (∀ ζ ∈ Z, v R ≤ v (z - ζ)) → v (p.eval z) = gauss ph := by
    intro z hz hzZ
    rw [← hph_ev z]
    refine v_eval_eq_gauss ph (v_hat_eq_one c hR hz).le fun β hβ hβ1 => ?_
    have hζ : c + R * β ∈ Z := by
      rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_map.2 ⟨β, hβ, rfl⟩
    have h1 := hzZ _ hζ
    have : (z - c) / R - β = (z - (c + R * β)) / R := by field_simp; ring
    rw [this, map_div₀, le_div_iff₀ hvRpos, one_mul]
    exact h1

  obtain ⟨u, hu1, hu⟩ := exists_generic_unit' (K := K)
    (ph.roots + qh.roots + (E.val.map fun e => (e - c) / R))
  set w : K := c + R * u with hw
  have hwhat : (w - c) / R = u := by rw [hw]; field_simp; ring
  have hwc : v (w - c) = v R := by
    have : w - c = R * u := by rw [hw]; ring
    rw [this, map_mul, hu1, mul_one]
  have hwE : ∀ e ∈ E, v R ≤ v (w - e) := by
    intro e he
    have hmem : (e - c) / R ∈ ph.roots + qh.roots + (E.val.map fun e => (e - c) / R) :=
      Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨e, Finset.mem_def.mp he, rfl⟩))
    have h1 := hu _ hmem
    have : w - e = R * (u - (e - c) / R) := by rw [hw]; field_simp; ring
    rw [this, map_mul]
    calc v R = v R * 1 := (mul_one _).symm
      _ ≤ v R * v (u - (e - c) / R) := mul_le_mul' le_rfl h1
  have hwS : w ∈ S := hS w hwc hwE
  have hwZ : ∀ ζ ∈ Z, v R ≤ v (w - ζ) := by
    intro ζ hζ
    rw [hZ, Multiset.mem_toFinset] at hζ
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hζ
    have hmem : β ∈ ph.roots + qh.roots + (E.val.map fun e => (e - c) / R) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl hβ)))
    have h1 := hu _ hmem
    have : w - (c + R * β) = R * (u - β) := by rw [hw]; ring
    rw [this, map_mul]
    calc v R = v R * 1 := (mul_one _).symm
      _ ≤ v R * v (u - β) := mul_le_mul' le_rfl h1

  set s : K := (r N).evalAt w with hs
  have hGq : gauss qh ≠ 0 := by
    intro h0
    have := hvq w hwc hwE
    rw [h0, (Valuation.zero_iff _)] at this
    exact hqz ⟨w, hwS⟩ this
  have hGqpos : 0 < gauss qh := zero_lt_iff.2 hGq
  have hvs : v s = gauss ph / gauss qh := by
    rw [hs, hev ⟨w, hwS⟩, map_div₀]
    simp only
    rw [hvp_eq w hwc hwZ, hvq w hwc hwE]

  have hr_le : ∀ z : ↥S, v ((z : K) - c) = v R → (∀ e ∈ E, v R ≤ v ((z : K) - e)) →
      v ((r N).evalAt z) ≤ v s := by
    intro z hz hzE
    rw [hvs, hev z, map_div₀, hvq z hz hzE]
    exact div_le_div_of_nonneg_right (hvp_le z hz) hGqpos.le
  have hr_eq : ∀ z : ↥S, v ((z : K) - c) = v R → (∀ e ∈ E, v R ≤ v ((z : K) - e)) →
      (∀ ζ ∈ Z, v R ≤ v ((z : K) - ζ)) → v ((r N).evalAt z) = v s := by
    intro z hz hzE hzZ
    rw [hvs, hev z, map_div₀, hvq z hz hzE, hvp_eq z hz hzZ]

  have hz₀r : v ((r N).evalAt z₀) = v (f z₀) :=
    Valuation.map_eq_of_sub_lt _ (hclose z₀)
  have hηs : v (f z₀) ≤ v s := hz₀r ▸ hr_le z₀ hz₀c hz₀E
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at hηs
    exact hfz₀ hηs
  refine ⟨s, hs0, Z, fun z hz hzE => ?_, fun z hz hzE hzZ => ?_⟩
  · have : f z = (r N).evalAt z - ((r N).evalAt z - f z) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le (hr_le z hz hzE) ((hclose z).le.trans hηs))
  · have hlt : v ((r N).evalAt z - f z) < v ((r N).evalAt z) := by
      rw [hr_eq z hz hzE hzZ]; exact (hclose z).trans_le hηs
    have : f z = (r N).evalAt z - ((r N).evalAt z - f z) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ hlt, hr_eq z hz hzE hzZ]

end P2mKcGenericModulus

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0) (E : Finset K)
    (hS : ∀ z : K, Valued.v (z - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v (z - e)) → z ∈ S)
    (h₀ : ∃ z : ↥S, Valued.v ((z : K) - c) = Valued.v R ∧ (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ Z : Finset K,
      (∀ z : ↥S, Valued.v ((z : K) - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) →
        Valued.v (f z) ≤ Valued.v s) ∧
      (∀ z : ↥S, Valued.v ((z : K) - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) →
        (∀ ζ ∈ Z, Valued.v R ≤ Valued.v ((z : K) - ζ)) → Valued.v (f z) = Valued.v s) :=
  P2mKcGenericModulus.main hf c R hR E hS h₀

end
end S_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn (solution)
