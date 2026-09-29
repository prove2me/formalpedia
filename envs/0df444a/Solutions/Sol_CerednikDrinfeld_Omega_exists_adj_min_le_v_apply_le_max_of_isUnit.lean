-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_adj_min_le_v_apply_le_max_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0245d0eb-8a6a-59d6-a9bc-12956b8130a2

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

open scoped MatrixGroups
open Polynomial CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.BruhatTits LT.LatticeTree

noncomputable section

namespace UAdj

section Order

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

theorem le_of_mul_le_mul_right0 {a b c : Γ₀} (h : a * c ≤ b * c) (hc : c ≠ 0) : a ≤ b := by
  simpa [mul_inv_cancel_right₀ hc] using mul_le_mul_left h c⁻¹

theorem eq_of_mul_eq_one_of_le_one {a b : Γ₀} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  push Not at hlt
  have : a * b < 1 := by
    calc a * b ≤ a * 1 := mul_le_mul_right hb a
      _ < 1 := by rw [mul_one]; exact hlt
  exact this.ne h

theorem ne_zpow_of_between {p t : Γ₀} (hp0 : 0 < p) (hp1 : p < 1) (h1 : p < t) (h2 : t < 1) (e : ℤ) : t ≠ p ^ e := by
  intro ht
  rcases le_or_gt e 0 with he | he
  · have : (1 : Γ₀) ≤ p ^ e := by
      rcases he.lt_or_eq with he | he
      · exact (one_lt_zpow_of_neg₀ hp0 hp1 he).le
      · rw [he, zpow_zero]
    exact not_lt.2 this (ht ▸ h2)
  · have : p ^ e ≤ p := by
      have h1e : (1 : ℤ) ≤ e := he
      calc p ^ e ≤ p ^ (1 : ℤ) := (zpow_right_strictAnti₀ hp0 hp1).antitone h1e
        _ = p := zpow_one p
    exact not_lt.2 this (ht ▸ h1)

end Order

section Frame

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem algebraMap_ne_zero_of_ne_zero {x : R} (hx : x ≠ 0) : algebraMap K₀ K (algebraMap R K₀ x) ≠ 0 := by
  rw [map_ne_zero_iff _ (algebraMap K₀ K).injective]
  exact fun h => hx (IsFractionRing.injective R K₀ (by rw [h, map_zero]))

theorem p_pos {ϖ : R} (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  (Valuation.pos_iff _).2 (algebraMap_ne_zero_of_ne_zero hϖ.ne_zero)

theorem v_unit_eq_one (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  have h := hint (u : R)
  have h' := hint ((u⁻¹ : Rˣ) : R)
  have hprod : Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ((u⁻¹ : Rˣ) : R))) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
  exact eq_of_mul_eq_one_of_le_one h h' hprod

theorem exists_v_eq_zpow {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ e : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ e := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero, zero_div])
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  refine ⟨(n : ℤ) - n', ?_⟩
  have hp0 := (p_pos (K₀ := K₀) (K := K) hϖ).ne'
  simp only [map_div₀, map_mul, map_pow, v_unit_eq_one hint, one_mul]
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]

theorem p_lt_one {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  refine lt_of_le_of_ne (hint ϖ) fun h => ?_
  have hne : ϖ₁.ϖ ≠ 0 := by
    intro h0
    have := ϖ₁.pos
    rw [h0, map_zero, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨e, he⟩ := exists_v_eq_zpow hϖ hint ϖ₁.ϖ hne
  rw [h, one_zpow] at he
  exact absurd ϖ₁.lt_one (by rw [he]; exact lt_irrefl 1)

theorem exists_v_pseudo_eq_pow {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) :
    ∃ m : ℕ, 1 ≤ m ∧ Valued.v (algebraMap K₀ K ϖ₁.ϖ) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m := by
  have hne : ϖ₁.ϖ ≠ 0 := by
    intro h0
    have := ϖ₁.pos
    rw [h0, map_zero, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨e, he⟩ := exists_v_eq_zpow hϖ hint ϖ₁.ϖ hne
  have hp0 := p_pos (K₀ := K₀) (K := K) hϖ
  have hp1 := p_lt_one hϖ hint ϖ₁
  rcases le_or_gt 1 e with h1 | h1
  · refine ⟨e.toNat, by omega, ?_⟩
    rw [he, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · exfalso
    have : (1 : Γ₀) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ e := by
      have he0 : e ≤ 0 := by omega
      rcases he0.lt_or_eq with he0 | he0
      · exact (one_lt_zpow_of_neg₀ hp0 hp1 he0).le
      · rw [he0, zpow_zero]
    exact not_lt.2 this (he ▸ ϖ₁.lt_one)

theorem v_pseudo_le_p {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) :
    Valued.v (algebraMap K₀ K ϖ₁.ϖ) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) := by
  obtain ⟨m, hm, he⟩ := exists_v_pseudo_eq_pow hϖ hint ϖ₁
  rw [he]
  calc _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ 1 :=
        pow_le_pow_right_of_le_one' (p_lt_one hϖ hint ϖ₁).le hm
    _ = _ := pow_one _

theorem exists_rep_v_sub_lt_one {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    (a : K₀) (ha : Valued.v (algebraMap K₀ K a) ≤ 1) :
    ∃ c : R ⧸ Ideal.span {ϖ},
      Valued.v (algebraMap K₀ K a - algebraMap K₀ K (algebraMap R K₀ (Quotient.out c))) < 1 := by
  obtain ⟨r, hr⟩ := hv a ha
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  have hcs : r - Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) r) ∈ Ideal.span {ϖ} := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 hcs
  rw [← hr, ← map_sub, ← map_sub, hs, map_mul, map_mul, Valuation.map_mul]
  calc _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) * 1 := mul_le_mul_right (hint s) _
    _ < 1 := by rw [mul_one]; exact p_lt_one hϖ hint ϖ₁

end Frame

section Generic

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem exists_generic [IsAlgClosed K] (B : Multiset K) : ∃ y : K, v y ≤ 1 ∧ ∀ b ∈ B, v b ≤ 1 → 1 ≤ v (y - b) := by
  classical
  let L : Multiset K := (0 : K) ::ₘ B.filter fun b => v b ≤ 1
  have hL : ∀ b ∈ L, v b ≤ 1 := fun b hb => by
    rcases Multiset.mem_cons.1 hb with rfl | hb
    · rw [map_zero]; exact zero_le'
    · exact (Multiset.mem_filter.1 hb).2
  let F : K[X] := (L.map fun b => X - C b).prod + 1
  have hmonic : (L.map fun b => X - C b).prod.Monic := monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  have hdegprod : (L.map fun b => X - C b).prod.natDegree = Multiset.card L := natDegree_multiset_prod_X_sub_C_eq_card L
  have hcard : 0 < Multiset.card L := Multiset.card_pos.2 (Multiset.cons_ne_zero)
  have hdeg' : (L.map fun b => X - C b).prod.degree = (Multiset.card L : WithBot ℕ) := by
    rw [degree_eq_natDegree hmonic.ne_zero, hdegprod]
  have hFmonic : F.Monic := hmonic.add_of_left (by rw [degree_one, hdeg']; exact_mod_cast hcard)
  have hFdeg : F.degree ≠ 0 := by
    have h1 : F.natDegree = Multiset.card L := by
      rw [show F = (L.map fun b => X - C b).prod + C 1 by rw [C_1], natDegree_add_C, hdegprod]
    rw [degree_eq_natDegree hFmonic.ne_zero, h1]
    exact_mod_cast hcard.ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root F hFdeg
  have hprod : (L.map fun b => y - b).prod = -1 := by
    have h := hy
    rw [IsRoot, eval_add, eval_one, eval_multiset_prod, Multiset.map_map, add_eq_zero_iff_eq_neg] at h
    simpa [Function.comp_def] using h
  have hvprod : (L.map fun b => v (y - b)).prod = 1 := by
    have := congrArg (Valued.v (R := K) (Γ₀ := Γ₀)) hprod
    rwa [map_multiset_prod, Multiset.map_map, Valuation.map_neg, map_one] at this
  have hy1 : v y ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have heq : (L.map fun b => v (y - b)) = L.map fun _ => v y :=
      Multiset.map_congr rfl fun b hb => Valuation.map_sub_eq_of_lt_left _ ((hL b hb).trans_lt hlt)
    rw [heq, Multiset.map_const', Multiset.prod_replicate] at hvprod
    exact absurd hvprod (ne_of_gt (lt_of_lt_of_le hlt (le_self_pow₀ hlt.le hcard.ne')))
  refine ⟨y, hy1, fun b hb hb1 => ?_⟩
  have hbL : b ∈ L := Multiset.mem_cons_of_mem (Multiset.mem_filter.2 ⟨hb, hb1⟩)
  have hle : ∀ b' ∈ L, v (y - b') ≤ 1 := fun b' hb' => (Valuation.map_sub _ _ _).trans (max_le hy1 (hL b' hb'))
  by_contra hlt
  push Not at hlt
  obtain ⟨L', hL'⟩ := Multiset.exists_cons_of_mem hbL
  have hprod_le : ∀ M : Multiset K, (∀ b' ∈ M, v (y - b') ≤ 1) → (M.map fun b' => v (y - b')).prod ≤ 1 := by
    intro M
    induction M using Multiset.induction_on with
    | empty => intro; simp
    | cons a M ih =>
      intro h
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_le_one' (h a (Multiset.mem_cons_self _ _)) (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))
  have hrest : (L'.map fun b' => v (y - b')).prod ≤ 1 :=
    hprod_le L' fun b' hb' => hle b' (hL' ▸ Multiset.mem_cons_of_mem hb')
  rw [hL', Multiset.map_cons, Multiset.prod_cons] at hvprod
  have : v (y - b) * (L'.map fun b' => v (y - b')).prod < 1 :=
    calc _ ≤ v (y - b) * 1 := mul_le_mul' le_rfl hrest
      _ < 1 := by rw [mul_one]; exact hlt
  exact absurd hvprod this.ne

end Generic

section AffinoidZero

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem exists_mem_affinoid_zero {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K) : ∃ ω : K, ω ∈ affinoid ϖ₁ 0 := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  let T : Multiset K :=
    (Finset.univ : Finset (R ⧸ Ideal.span {ϖ})).val.map fun c => algebraMap K₀ K (algebraMap R K₀ (Quotient.out c))
  obtain ⟨y, hy1, hgen⟩ := exists_generic (K := K) (Γ₀ := Γ₀) T
  refine ⟨y, ?_⟩
  rw [mem_affinoid_iff']
  refine ⟨by rw [pow_zero]; exact hy1, fun a => ?_⟩
  rw [pow_zero]
  rcases le_or_gt (Valued.v (algebraMap K₀ K a)) 1 with ha | ha
  · obtain ⟨c, hc⟩ := exists_rep_v_sub_lt_one hϖ hint hv ϖ₁ a ha
    set t : K := algebraMap K₀ K (algebraMap R K₀ (Quotient.out c)) with ht
    have ht1 : Valued.v t ≤ 1 := hint _
    have htT : t ∈ T := Multiset.mem_map.2 ⟨c, Finset.mem_univ_val c, rfl⟩
    have h1 : 1 ≤ Valued.v (y - t) := hgen t htT ht1
    have hlt : Valued.v (t - algebraMap K₀ K a) < Valued.v (y - t) := by
      rw [← Valuation.map_neg, neg_sub]; exact hc.trans_le h1
    rw [show y - algebraMap K₀ K a = (y - t) + (t - algebraMap K₀ K a) by ring, Valuation.map_add_eq_of_lt_left _ hlt]
    exact h1
  · rw [Valuation.map_sub_eq_of_lt_right _ (hy1.trans_lt ha)]
    exact ha.le

end AffinoidZero

section Nearest

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem exists_nearest {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ a₀ : K₀, ∀ a : K₀, Valued.v (z - algebraMap K₀ K a₀) ≤ Valued.v (z - algebraMap K₀ K a) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hp
  have hp0 : 0 < p := p_pos hϖ
  have hp1 : p < 1 := p_lt_one hϖ hint ϖ₁
  by_cases hA : ∃ a₁ : K₀, ∀ e : ℤ, Valued.v (z - algebraMap K₀ K a₁) ≠ p ^ e
  · obtain ⟨a₁, ha₁⟩ := hA
    refine ⟨a₁, fun a => ?_⟩
    by_cases haa : a = a₁
    · rw [haa]
    · obtain ⟨e, he⟩ := exists_v_eq_zpow hϖ hint (a₁ - a) (sub_ne_zero.2 (Ne.symm haa))
      have hne : Valued.v (z - algebraMap K₀ K a₁) ≠ Valued.v (algebraMap K₀ K (a₁ - a)) := by
        rw [he]; exact ha₁ e
      have hsplit : z - algebraMap K₀ K a = (z - algebraMap K₀ K a₁) + algebraMap K₀ K (a₁ - a) := by
        rw [map_sub]; ring
      rcases lt_or_gt_of_ne hne with h | h
      · rw [hsplit, Valuation.map_add_eq_of_lt_right _ h]; exact h.le
      · rw [hsplit, Valuation.map_add_eq_of_lt_left _ h]
  · push Not at hA
    obtain ⟨n, hn⟩ := hex z hz
    obtain ⟨m, hm1, hm⟩ := exists_v_pseudo_eq_pow hϖ hint ϖ₁
    have hlow : ∀ a : K₀, p ^ ((m * n : ℕ) : ℤ) ≤ Valued.v (z - algebraMap K₀ K a) := fun a => by
      rw [zpow_natCast, pow_mul, ← hm]
      exact ((mem_affinoid_iff' ϖ₁ n z).1 hn).2 a
    have hbdd : ∀ e : ℤ, (∃ a : K₀, Valued.v (z - algebraMap K₀ K a) = p ^ e) → e ≤ (m * n : ℕ) := by
      rintro e ⟨a, ha⟩
      have := hlow a
      rw [ha] at this
      exact (zpow_right_strictAnti₀ hp0 hp1).le_iff_ge.1 this
    obtain ⟨e₀, he₀⟩ := hA 0
    obtain ⟨ub, ⟨a₀, ha₀⟩, hub⟩ :=
      Int.exists_greatest_of_bdd (P := fun e : ℤ => ∃ a : K₀, Valued.v (z - algebraMap K₀ K a) = p ^ e)
        ⟨_, hbdd⟩ ⟨e₀, 0, he₀⟩
    refine ⟨a₀, fun a => ?_⟩
    obtain ⟨e, he⟩ := hA a
    have hle : e ≤ ub := hub e ⟨a, he⟩
    rw [ha₀, he]
    exact (zpow_right_strictAnti₀ hp0 hp1).antitone hle

theorem exists_chart {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    ∃ (k : ℤ) (a₀ : K₀) (y : K), z = algebraMap K₀ K (algebraMap R K₀ ϖ ^ k) * y + algebraMap K₀ K a₀ ∧
      ((Valued.v y = 1 ∧ ∀ b : K₀, 1 ≤ Valued.v (y - algebraMap K₀ K b)) ∨
        (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < Valued.v y ∧ Valued.v y < 1)) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hp
  have hp0 : 0 < p := p_pos hϖ
  have hp1 : p < 1 := p_lt_one hϖ hint ϖ₁
  have hpne : p ≠ 0 := hp0.ne'
  have hϖK : algebraMap K₀ K (algebraMap R K₀ ϖ) ≠ 0 := algebraMap_ne_zero_of_ne_zero hϖ.ne_zero
  obtain ⟨a₀, ha₀⟩ := exists_nearest hϖ hint ϖ₁ hex hz
  set r : Γ₀ := Valued.v (z - algebraMap K₀ K a₀) with hr
  have hr0 : 0 < r := by
    rw [hr, Valuation.pos_iff]
    intro h0
    rw [mem_upperHalfPlane_iff] at hz
    exact hz a₀ (sub_eq_zero.1 h0).symm

  have chart : ∀ k : ℤ, ∃ y : K, z = algebraMap K₀ K (algebraMap R K₀ ϖ ^ k) * y + algebraMap K₀ K a₀ ∧
      Valued.v y = r / p ^ k ∧
      ∀ b : K₀, r / p ^ k ≤ Valued.v (y - algebraMap K₀ K b) := by
    intro k
    set π : K := algebraMap K₀ K (algebraMap R K₀ ϖ ^ k) with hπ
    have hπv : Valued.v π = p ^ k := by rw [hπ, map_zpow₀, map_zpow₀]
    have hπ0 : π ≠ 0 := by rw [hπ, map_zpow₀]; exact zpow_ne_zero k hϖK
    refine ⟨(z - algebraMap K₀ K a₀) / π, by rw [mul_div_cancel₀ _ hπ0, sub_add_cancel], by
      rw [map_div₀, hπv], fun b => ?_⟩
    have : (z - algebraMap K₀ K a₀) / π - algebraMap K₀ K b =
        (z - algebraMap K₀ K (a₀ + algebraMap R K₀ ϖ ^ k * b)) / π := by
      rw [eq_div_iff hπ0, sub_mul, div_mul_cancel₀ _ hπ0, map_add, map_mul, ← hπ]; ring
    rw [this, map_div₀, hπv, div_le_div_iff_of_pos_right (zpow_pos hp0 k)]
    exact ha₀ _
  by_cases hk : ∃ k : ℤ, r = p ^ k
  · obtain ⟨k, hk⟩ := hk
    obtain ⟨y, hzy, hvy, hby⟩ := chart k
    have hrk : r / p ^ k = 1 := by rw [hk, div_self (zpow_ne_zero k hpne)]
    refine ⟨k, a₀, y, hzy, Or.inl ⟨by rw [hvy, hrk], fun b => by rw [← hrk]; exact hby b⟩⟩
  · push Not at hk

    obtain ⟨n, hn⟩ := hex z hz
    obtain ⟨m, hm1, hm⟩ := exists_v_pseudo_eq_pow hϖ hint ϖ₁
    have hlow : p ^ ((m * n : ℕ) : ℤ) ≤ r := by
      rw [zpow_natCast, pow_mul, ← hm]
      exact ((mem_affinoid_iff' ϖ₁ n z).1 hn).2 a₀
    have hup : r < p ^ (-((m * n : ℕ) : ℤ) - 1) := by
      have h1 : r ≤ Valued.v z := by simpa using ha₀ 0
      have h2 : Valued.v z ≤ p ^ (-((m * n : ℕ) : ℤ)) := by
        have := ((mem_affinoid_iff' ϖ₁ n z).1 hn).1
        rw [hm, ← inv_pow, ← pow_mul] at this
        rwa [zpow_neg, zpow_natCast, ← inv_pow]
      refine (h1.trans h2).trans_lt ?_
      exact (zpow_right_strictAnti₀ hp0 hp1) (by omega)
    obtain ⟨k, hk1, hk2⟩ :=
      Int.exists_greatest_of_bdd (P := fun j : ℤ => r < p ^ j) ⟨(m * n : ℕ), fun j hj => by
        have := hlow.trans_lt hj
        exact ((zpow_right_strictAnti₀ hp0 hp1).lt_iff_gt.1 this).le⟩ ⟨_, hup⟩
    have hk3 : p ^ (k + 1) < r := by
      refine lt_of_le_of_ne (not_lt.1 fun h => ?_) (hk (k + 1)).symm
      have := hk2 (k + 1) h
      omega
    obtain ⟨y, hzy, hvy, hby⟩ := chart k
    refine ⟨k, a₀, y, hzy, Or.inr ⟨?_, ?_⟩⟩
    · rw [hvy, lt_div_iff₀ (zpow_pos hp0 k), mul_comm, ← zpow_add_one₀ hpne]
      exact hk3
    · rw [hvy, div_lt_iff₀ (zpow_pos hp0 k), one_mul]
      exact hk1

end Nearest

section Region

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

variable (K₀) in

def edgeRegion (p : Γ₀) : Set K :=
  {y | (Valued.v y = 1 ∧ ∀ a : K₀, 1 ≤ Valued.v (y - algebraMap K₀ K a)) ∨
    (p < Valued.v y ∧ Valued.v y < 1) ∨
    (Valued.v y = p ∧ ∀ a : K₀, p ≤ Valued.v (y - algebraMap K₀ K a))}

theorem p_le_v_of_mem_edgeRegion {p : Γ₀} (hp1 : p ≤ 1) {y : K} (hy : y ∈ edgeRegion K₀ (K := K) p) :
    p ≤ Valued.v y := by
  rcases hy with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact hp1
  · exact h1.le
  · rw [h1]

theorem v_le_one_of_mem_edgeRegion {p : Γ₀} (hp1 : p ≤ 1) {y : K} (hy : y ∈ edgeRegion K₀ (K := K) p) :
    Valued.v y ≤ 1 := by
  rcases hy with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨h1, -⟩
  · rw [h1]
  · exact h1.le
  · rw [h1]; exact hp1

theorem v_ne_zero_of_mem_edgeRegion {p : Γ₀} (hp0 : 0 < p) (hp1 : p ≤ 1) {y : K}
    (hy : y ∈ edgeRegion K₀ (K := K) p) : Valued.v y ≠ 0 :=
  (hp0.trans_le (p_le_v_of_mem_edgeRegion hp1 hy)).ne'

theorem mem_edgeRegion_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) (p : Γ₀) {w : K}
    (hw : w ∈ affinoid ϖ₁ 0) : w ∈ edgeRegion K₀ (K := K) p := by
  rw [mem_affinoid_iff'] at hw
  obtain ⟨hw1, hw2⟩ := hw
  simp only [pow_zero] at hw1 hw2
  refine Or.inl ⟨le_antisymm hw1 (by simpa using hw2 0), hw2⟩

theorem smul_mem_edgeRegion {ϖ : R} (hϖ : Irreducible ϖ) (ϖ₁ : PseudoUniformizer K₀ K) {w : K}
    (hw : w ∈ affinoid ϖ₁ 0) :
    algebraMap K₀ K (algebraMap R K₀ ϖ) * w ∈
      edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hp
  have hπ0 : algebraMap K₀ K (algebraMap R K₀ ϖ) ≠ 0 := algebraMap_ne_zero_of_ne_zero hϖ.ne_zero
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective R K₀ (by rw [h, map_zero]))
  rw [mem_affinoid_iff'] at hw
  obtain ⟨hw1, hw2⟩ := hw
  simp only [pow_zero] at hw1 hw2
  have hvw : Valued.v w = 1 := le_antisymm hw1 (by simpa using hw2 0)
  refine Or.inr (Or.inr ⟨by rw [Valuation.map_mul, hvw, mul_one], fun a => ?_⟩)
  have : algebraMap K₀ K (algebraMap R K₀ ϖ) * w - algebraMap K₀ K a =
      algebraMap K₀ K (algebraMap R K₀ ϖ) * (w - algebraMap K₀ K (a / algebraMap R K₀ ϖ)) := by
    rw [map_div₀, mul_sub, mul_div_cancel₀ _ hπ0]
  rw [this, Valuation.map_mul]
  calc p = p * 1 := (mul_one p).symm
    _ ≤ _ := mul_le_mul_right (hw2 _) _

theorem edgeRegion_subset_affinoid_one {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (ϖ₁ : PseudoUniformizer K₀ K) :
    edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))) ⊆ affinoid ϖ₁ 1 := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hp
  have hp0 : 0 < p := p_pos hϖ
  have hp1 : p < 1 := p_lt_one hϖ hint ϖ₁
  have hq : Valued.v (algebraMap K₀ K ϖ₁.ϖ) ≤ p := v_pseudo_le_p hϖ hint ϖ₁
  intro y hy
  rw [mem_affinoid_iff', pow_one, pow_one]
  refine ⟨(v_le_one_of_mem_edgeRegion hp1.le hy).trans ((one_le_inv₀ ϖ₁.pos).2 ϖ₁.lt_one.le), fun a => hq.trans ?_⟩
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hp1.le.trans (h2 a)
  ·
    by_cases ha : a = 0
    · rw [ha, map_zero, sub_zero]; exact h1.le
    · obtain ⟨e, he⟩ := exists_v_eq_zpow hϖ hint a ha
      have hne : Valued.v y ≠ Valued.v (algebraMap K₀ K a) := by
        rw [he]; exact ne_zpow_of_between hp0 hp1 h1 h2 e
      rcases lt_or_gt_of_ne hne with h | h
      · rw [Valuation.map_sub_eq_of_lt_right _ h]; exact (h1.trans h).le
      · rw [Valuation.map_sub_eq_of_lt_left _ h]; exact h1.le
  · exact h2 a

theorem edgeRegion_subset_upperHalfPlane {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (ϖ₁ : PseudoUniformizer K₀ K) :
    edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))) ⊆ upperHalfPlane K₀ K :=
  (edgeRegion_subset_affinoid_one hϖ hint ϖ₁).trans (affinoid_subset_upperHalfPlane ϖ₁ 1)

theorem root_dichotomy {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (ϖ₁ : PseudoUniformizer K₀ K) {β : K}
    (hβ : β ∉ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))) :
    (∃ c : Γ₀, c ≠ 0 ∧ ∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))),
        Valued.v (y - β) = c) ∨
      (∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))),
        Valued.v (y - β) = Valued.v y) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hp
  have hp0 : 0 < p := p_pos hϖ
  have hp1 : p < 1 := p_lt_one hϖ hint ϖ₁
  rcases lt_trichotomy (Valued.v β) p with h | h | h
  ·
    right
    intro y hy
    exact Valuation.map_sub_eq_of_lt_left _ (h.trans_le (p_le_v_of_mem_edgeRegion hp1.le hy))
  ·
    have : ¬ ∀ a : K₀, p ≤ Valued.v (β - algebraMap K₀ K a) := fun hall => hβ (Or.inr (Or.inr ⟨h, hall⟩))
    push Not at this
    obtain ⟨a, ha⟩ := this
    have hva : Valued.v (algebraMap K₀ K a) = p := by
      have := Valuation.map_sub_eq_of_lt_left (Valued.v (R := K)) (x := β) (y := β - algebraMap K₀ K a) (ha.trans_eq h.symm)
      rwa [sub_sub_cancel, h] at this
    right
    intro y hy
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · exact Valuation.map_sub_eq_of_lt_left _ (by rw [h, hy1]; exact hp1)
    · exact Valuation.map_sub_eq_of_lt_left _ (by rw [h]; exact hy1)
    · have hlt : Valued.v (β - algebraMap K₀ K a) < Valued.v (y - algebraMap K₀ K a) := ha.trans_le (hy2 a)
      rw [show y - β = (y - algebraMap K₀ K a) - (β - algebraMap K₀ K a) by ring, Valuation.map_sub_eq_of_lt_left _ hlt]
      refine le_antisymm ?_ (hy1 ▸ hy2 a)
      rw [hy1]
      exact (Valuation.map_sub _ _ _).trans (max_le hy1.le hva.le)
  · rcases lt_trichotomy (Valued.v β) 1 with h' | h' | h'
    · exact absurd (Or.inr (Or.inl ⟨h, h'⟩)) hβ
    ·
      have : ¬ ∀ a : K₀, 1 ≤ Valued.v (β - algebraMap K₀ K a) := fun hall => hβ (Or.inl ⟨h', hall⟩)
      push Not at this
      obtain ⟨a, ha⟩ := this
      have hva : Valued.v (algebraMap K₀ K a) = 1 := by
        have := Valuation.map_sub_eq_of_lt_left (Valued.v (R := K)) (x := β) (y := β - algebraMap K₀ K a)
          (ha.trans_eq h'.symm)
        rwa [sub_sub_cancel, h'] at this
      left
      refine ⟨1, one_ne_zero, fun y hy => ?_⟩
      have hya : Valued.v (y - algebraMap K₀ K a) = 1 := by
        rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
        · exact le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hy1.le hva.le)) (hy2 a)
        · rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hva]; exact hy2), hva]
        · rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hva, hy1]; exact hp1), hva]
      have hlt : Valued.v (β - algebraMap K₀ K a) < Valued.v (y - algebraMap K₀ K a) := by rw [hya]; exact ha
      rw [show y - β = (y - algebraMap K₀ K a) - (β - algebraMap K₀ K a) by ring, Valuation.map_sub_eq_of_lt_left _ hlt,
        hya]
    ·
      left
      refine ⟨Valued.v β, (zero_lt_one.trans h').ne', fun y hy => ?_⟩
      exact Valuation.map_sub_eq_of_lt_right _ ((v_le_one_of_mem_edgeRegion hp1.le hy).trans_lt h')

theorem multiset_prod_monomial {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (ϖ₁ : PseudoUniformizer K₀ K)
    (s : Multiset K) (hs : ∀ β ∈ s, β ∉ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))) :
    ∃ C : Γ₀, C ≠ 0 ∧ ∃ m : ℕ, ∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))),
      (s.map fun β => Valued.v (y - β)).prod = C * Valued.v y ^ m := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, one_ne_zero, 0, fun y _ => by simp⟩
  | cons β s ih =>
    obtain ⟨C, hC, m, hm⟩ := ih fun β' hβ' => hs β' (Multiset.mem_cons_of_mem hβ')
    rcases root_dichotomy hϖ hint ϖ₁ (hs β (Multiset.mem_cons_self _ _)) with ⟨c, hc, hcst⟩ | hlin
    · refine ⟨c * C, mul_ne_zero hc hC, m, fun y hy => ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, hcst y hy, hm y hy, mul_assoc]
    · refine ⟨C, hC, m + 1, fun y hy => ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, hlin y hy, hm y hy, mul_comm (Valued.v y) _, mul_assoc, ← pow_succ]

theorem eq_C_mul_prod [IsAlgClosed K] (P : K[X]) : P = C P.leadingCoeff * (P.roots.map fun α => X - C α).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((splits_iff_card_roots.1 (IsAlgClosed.splits P)).symm ▸ rfl)).symm

theorem v_eval_monomial [IsAlgClosed K] {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (ϖ₁ : PseudoUniformizer K₀ K)
    (P : K[X]) (hP0 : P ≠ 0)
    (hP : ∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))), P.eval y ≠ 0) :
    ∃ C : Γ₀, C ≠ 0 ∧ ∃ m : ℕ, ∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))),
      Valued.v (P.eval y) = C * Valued.v y ^ m := by
  have hroots : ∀ β ∈ P.roots, β ∉ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))) :=
    fun β hβ hmem => hP β hmem ((mem_roots hP0).1 hβ)
  obtain ⟨C₀, hC, m, hm⟩ := multiset_prod_monomial hϖ hint ϖ₁ P.roots hroots
  refine ⟨Valued.v P.leadingCoeff * C₀, mul_ne_zero ((Valuation.ne_zero_iff _).2 (leadingCoeff_ne_zero.2 hP0)) hC, m,
    fun y hy => ?_⟩
  conv_lhs => rw [eq_C_mul_prod P]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Valuation.map_mul, map_multiset_prod, Multiset.map_map]
  have : (P.roots.map ((Valued.v (R := K)) ∘ eval y ∘ fun α => X - Polynomial.C α)) =
      P.roots.map fun β => Valued.v (y - β) :=
    Multiset.map_congr rfl fun β _ => by simp
  rw [this, hm y hy, mul_assoc]

theorem coe_mul_apply (ϖ₁ : PseudoUniformizer K₀ K) (f g : ↥(holRing ϖ₁)) (z : ↥(upperHalfPlane K₀ K)) :
    ((f * g : ↥(holRing ϖ₁)) : ↥(upperHalfPlane K₀ K) → K) z =
      (f : ↥(upperHalfPlane K₀ K) → K) z * (g : ↥(upperHalfPlane K₀ K) → K) z := rfl

theorem apply_mul_inv_apply (ϖ₁ : PseudoUniformizer K₀ K) {f : ↥(holRing ϖ₁)} (hf : IsUnit f)
    (z : ↥(upperHalfPlane K₀ K)) :
    (f : ↥(upperHalfPlane K₀ K) → K) z * ((↑(hf.unit⁻¹) : ↥(holRing ϖ₁)) : ↥(upperHalfPlane K₀ K) → K) z = 1 := by
  have h1 := congrArg (fun F : ↥(holRing ϖ₁) => (F : ↥(upperHalfPlane K₀ K) → K) z) hf.unit.mul_inv
  simp only [coe_mul_apply, IsUnit.unit_spec] at h1
  exact h1

theorem apply_ne_zero_of_isUnit (ϖ₁ : PseudoUniformizer K₀ K) {f : ↥(holRing ϖ₁)} (hf : IsUnit f)
    (z : ↥(upperHalfPlane K₀ K)) : (f : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
  intro h0
  have h1 := apply_mul_inv_apply ϖ₁ hf z
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_ratPair_v_eq (ϖ₁ : PseudoUniformizer K₀ K) (F : ↥(holRing ϖ₁)) (hF : IsUnit F) (n : ℕ) :
    ∃ r : RatPair K, r.IsPoleFreeOn (affinoid ϖ₁ n) ∧
      ∀ (z : K) (hz : z ∈ affinoid ϖ₁ n),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨z, affinoid_subset_upperHalfPlane ϖ₁ n hz⟩) = Valued.v (r.evalAt z) := by
  obtain ⟨r, hr, -, hlim⟩ := (mem_holRing_iff ϖ₁ _).1 F.2 n
  set Fi : ↥(holRing ϖ₁) := ↑(hF.unit⁻¹) with hFi
  obtain ⟨Bd, hBd⟩ := ((mem_holRing_iff ϖ₁ _).1 Fi.2 n).bounded

  have hΩ := affinoid_subset_upperHalfPlane ϖ₁ n
  have hlow : ∀ (z : K) (hz : z ∈ affinoid ϖ₁ n),
      Valued.v Bd⁻¹ ≤ Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) ∧ Valued.v Bd ≠ 0 := by
    intro z hz
    have h1 := apply_mul_inv_apply ϖ₁ hF ⟨z, hΩ hz⟩
    rw [← hFi] at h1
    have h2 : Valued.v ((Fi : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) ≤ Valued.v Bd := hBd ⟨z, hz⟩
    have h3 : Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) *
        Valued.v ((Fi : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) = 1 := by
      rw [← Valuation.map_mul, h1, map_one]
    have hBd0 : Valued.v Bd ≠ 0 := by
      intro h0
      rw [h0, le_zero_iff] at h2
      rw [h2, mul_zero] at h3
      exact zero_ne_one h3
    refine ⟨?_, hBd0⟩
    rw [map_inv₀, inv_le_iff_one_le_mul₀ (zero_lt_iff.2 hBd0)]
    calc (1 : Γ₀) = _ := h3.symm
      _ ≤ _ := mul_le_mul_right h2 _
  rw [tendstoUniformly_iff_vRestrict] at hlim
  by_cases hne : (affinoid ϖ₁ n).Nonempty
  swap
  · refine ⟨r 0, hr 0, fun z hz => absurd ⟨z, hz⟩ hne⟩
  obtain ⟨z₀, hz₀⟩ := hne
  have hBd0 : Valued.v Bd ≠ 0 := (hlow z₀ hz₀).2
  have hBdi : vRestrict K Bd⁻¹ ≠ 0 := by
    rw [ne_eq, map_eq_zero, inv_eq_zero]; exact fun h => hBd0 (by rw [h, map_zero])
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hBdi))
  refine ⟨r N, hr N, fun z hz => ?_⟩
  have h1 : vRestrict K ((r N).evalAt z - (F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) < vRestrict K Bd⁻¹ :=
    hN N le_rfl ⟨z, hz⟩
  have h2 : vRestrict K Bd⁻¹ ≤ vRestrict K ((F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) :=
    (v_le_iff_vRestrict_le K _ _).1 (hlow z hz).1
  have h3 : vRestrict K ((r N).evalAt z) = vRestrict K ((F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) := by
    rw [show (r N).evalAt z = ((r N).evalAt z - (F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩) +
      (F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hΩ hz⟩ by ring]
    exact Valuation.map_add_eq_of_lt_right _ (h1.trans_le h2)
  exact ((Valuation.isEquiv_restrict (Valued.v (R := K))).val_eq.2 h3).symm

theorem exists_monomial_law [IsAlgClosed K] {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (ϖ₁ : PseudoUniformizer K₀ K)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ (CP CQ : Γ₀) (mP mQ : ℕ), CP ≠ 0 ∧ CQ ≠ 0 ∧
      ∀ (y : K) (hy : y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨y, edgeRegion_subset_upperHalfPlane hϖ hint ϖ₁ hy⟩) *
            (CQ * Valued.v y ^ mQ) = CP * Valued.v y ^ mP := by
  have hB1 := edgeRegion_subset_affinoid_one (K := K) hϖ hint ϖ₁
  obtain ⟨r, hr, hv⟩ := exists_ratPair_v_eq ϖ₁ F hF 1
  have hQ : ∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))), r.den.eval y ≠ 0 :=
    fun y hy => hr y (hB1 hy)
  have hP : ∀ y ∈ edgeRegion K₀ (K := K) (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ))), r.num.eval y ≠ 0 := by
    intro y hy h0
    have h1 := hv y (hB1 hy)
    rw [RatPair.evalAt, h0, zero_div, map_zero, Valuation.zero_iff] at h1
    exact apply_ne_zero_of_isUnit ϖ₁ hF _ h1
  by_cases hP0 : r.num = 0
  · refine ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero, fun y hy => absurd (by rw [hP0, eval_zero]) (hP y hy)⟩
  by_cases hQ0 : r.den = 0
  · refine ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero, fun y hy => absurd (by rw [hQ0, eval_zero]) (hQ y hy)⟩
  obtain ⟨CP, hCP, mP, hmP⟩ := v_eval_monomial hϖ hint ϖ₁ r.num hP0 hP
  obtain ⟨CQ, hCQ, mQ, hmQ⟩ := v_eval_monomial hϖ hint ϖ₁ r.den hQ0 hQ
  refine ⟨CP, CQ, mP, mQ, hCP, hCQ, fun y hy => ?_⟩
  rw [← hmP y hy, ← hmQ y hy, hv y (hB1 hy), RatPair.evalAt, map_div₀,
    div_mul_cancel₀ _ ((Valuation.ne_zero_iff _).2 (hQ y hy))]

theorem between_of_monomial_law {p : Γ₀} (hp0 : 0 < p) (hp1 : p < 1) {CP CQ : Γ₀} {mP mQ : ℕ} (hCP : CP ≠ 0)
    (hCQ : CQ ≠ 0) {a b c t : Γ₀} (ha : a * (CQ * 1 ^ mQ) = CP * 1 ^ mP) (hb : b * (CQ * p ^ mQ) = CP * p ^ mP)
    (hc : c * (CQ * t ^ mQ) = CP * t ^ mP) (ht1 : p < t) (ht2 : t < 1) :
    min a b ≤ c ∧ c ≤ max a b := by
  simp only [one_pow, mul_one] at ha
  have htne : t ≠ 0 := (hp0.trans ht1).ne'
  have hpne : p ≠ 0 := hp0.ne'
  rcases le_total mQ mP with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h

    have hc' : c * CQ = CP * t ^ d := by
      apply mul_right_cancel₀ (pow_ne_zero mQ htne)
      calc c * CQ * t ^ mQ = c * (CQ * t ^ mQ) := by rw [mul_assoc]
        _ = CP * t ^ (mQ + d) := hc
        _ = CP * t ^ d * t ^ mQ := by rw [pow_add]; ac_rfl
    have hb' : b * CQ = CP * p ^ d := by
      apply mul_right_cancel₀ (pow_ne_zero mQ hpne)
      calc b * CQ * p ^ mQ = b * (CQ * p ^ mQ) := by rw [mul_assoc]
        _ = CP * p ^ (mQ + d) := hb
        _ = CP * p ^ d * p ^ mQ := by rw [pow_add]; ac_rfl
    have h1 : b * CQ ≤ c * CQ := by
      rw [hb', hc']; exact mul_le_mul_right (pow_le_pow_left' ht1.le d) _
    have h2 : c * CQ ≤ a * CQ := by
      rw [hc', ha]
      calc CP * t ^ d ≤ CP * 1 ^ d := mul_le_mul_right (pow_le_pow_left' ht2.le d) _
        _ = CP := by rw [one_pow, mul_one]
    exact ⟨(min_le_right a b).trans (le_of_mul_le_mul_right0 h1 hCQ),
      (le_of_mul_le_mul_right0 h2 hCQ).trans (le_max_left a b)⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h

    have hc' : c * CQ * t ^ d = CP := by
      apply mul_right_cancel₀ (pow_ne_zero mP htne)
      calc c * CQ * t ^ d * t ^ mP = c * (CQ * t ^ (mP + d)) := by rw [pow_add]; ac_rfl
        _ = CP * t ^ mP := hc
    have hb' : b * CQ * p ^ d = CP := by
      apply mul_right_cancel₀ (pow_ne_zero mP hpne)
      calc b * CQ * p ^ d * p ^ mP = b * (CQ * p ^ (mP + d)) := by rw [pow_add]; ac_rfl
        _ = CP * p ^ mP := hb
    have h1 : a * CQ ≤ c * CQ := by
      have : c * CQ * t ^ d ≤ c * CQ * 1 ^ d := mul_le_mul_right (pow_le_pow_left' ht2.le d) _
      rw [one_pow, mul_one, hc', ← ha] at this
      exact this
    have h2 : c * CQ ≤ b * CQ := by
      have : b * CQ * p ^ d ≤ b * CQ * t ^ d := mul_le_mul_right (pow_le_pow_left' ht1.le d) _
      rw [hb', ← hc'] at this
      exact le_of_mul_le_mul_right0 this (pow_ne_zero d htne)
    exact ⟨(min_le_left a b).trans (le_of_mul_le_mul_right0 h1 hCQ),
      (le_of_mul_le_mul_right0 h2 hCQ).trans (le_max_right a b)⟩

end Region

section Geometry

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]

variable (K₀) in

def dMat {ϖ : R} (hϖ : Irreducible ϖ) : GL (Fin 2) K₀ := diagSnd (unitOfNeZero (K := K₀) hϖ.ne_zero)

theorem adj_stdVertex_dMat_inv_smul {ϖ : R} (hϖ : Irreducible ϖ) :
    (BruhatTits.tree R K₀).Adj (stdVertex R K₀) ((dMat K₀ hϖ)⁻¹ • stdVertex R K₀) := by
  have hV : VertRel R K₀ (stdVertex R K₀) (dMat K₀ hϖ • stdVertex R K₀) :=
    ⟨stdLattice R K₀, latticeMap (dMat K₀ hϖ) (stdLattice R K₀), isFullLattice_stdLattice,
      isFullLattice_stdLattice.map _, rfl, rfl, adjacentLattice_stdLattice_diagSnd hϖ⟩
  have hne : stdVertex R K₀ ≠ dMat K₀ hϖ • stdVertex R K₀ := fun h =>
    stdVertex_ne_act_diagSnd (K := K₀) hϖ h.symm
  have hadj : (BruhatTits.tree R K₀).Adj (stdVertex R K₀) (dMat K₀ hϖ • stdVertex R K₀) :=
    (tree_adj_iff _ _).2 ⟨hne, Or.inl hV⟩
  have := Mumford.GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (dMat K₀ hϖ)⁻¹ hadj
  rw [inv_smul_smul] at this
  exact this.symm

theorem pmoebius_dMat_inv {ϖ : R} (hϖ : Irreducible ϖ) {y : K} (hy : y ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (dMat K₀ hϖ)⁻¹) y = algebraMap K₀ K (algebraMap R K₀ ϖ) * y := by
  have h10 : ((dMat K₀ hϖ)⁻¹ : GL (Fin 2) K₀) 1 0 = 0 := by
    show Matrix.diagonal ![(1 : K₀), (((unitOfNeZero (K := K₀) hϖ.ne_zero)⁻¹ : K₀ˣ) : K₀)] 1 0 = 0
    simp
  have h11 : ((dMat K₀ hϖ)⁻¹ : GL (Fin 2) K₀) 1 1 = (algebraMap R K₀ ϖ)⁻¹ := by
    show Matrix.diagonal ![(1 : K₀), (((unitOfNeZero (K := K₀) hϖ.ne_zero)⁻¹ : K₀ˣ) : K₀)] 1 1 = _
    simp
  have h00 : ((dMat K₀ hϖ)⁻¹ : GL (Fin 2) K₀) 0 0 = 1 := by
    show Matrix.diagonal ![(1 : K₀), (((unitOfNeZero (K := K₀) hϖ.ne_zero)⁻¹ : K₀ˣ) : K₀)] 0 0 = 1
    simp
  have h01 : ((dMat K₀ hϖ)⁻¹ : GL (Fin 2) K₀) 0 1 = 0 := by
    show Matrix.diagonal ![(1 : K₀), (((unitOfNeZero (K := K₀) hϖ.ne_zero)⁻¹ : K₀ˣ) : K₀)] 0 1 = 0
    simp
  have hϖ0 : algebraMap K₀ K (algebraMap R K₀ ϖ) ≠ 0 := algebraMap_ne_zero_of_ne_zero hϖ.ne_zero
  rw [pmoebius_mk K₀ _ y (moebius_denom_ne_zero_of_mem K₀ hy _), moebius, h10, h11, h00, h01, map_zero, map_one,
    zero_mul, zero_add, one_mul, add_zero, map_inv₀, div_eq_mul_inv, inv_inv, mul_comm]

def chartMat {ϖ : R} (hϖ : Irreducible ϖ) (k : ℤ) (a₀ : K₀) : GL (Fin 2) K₀ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![algebraMap R K₀ ϖ ^ k, a₀; 0, 1] (by
    rw [Matrix.det_fin_two_of]
    have h0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective R K₀ (by rw [h, map_zero]))
    simpa using zpow_ne_zero k h0)

theorem pmoebius_chartMat {ϖ : R} (hϖ : Irreducible ϖ) (k : ℤ) (a₀ : K₀) {y : K} (hy : y ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (chartMat (K₀ := K₀) hϖ k a₀)) y =
      algebraMap K₀ K (algebraMap R K₀ ϖ ^ k) * y + algebraMap K₀ K a₀ := by
  have h10 : (chartMat (K₀ := K₀) hϖ k a₀ : GL (Fin 2) K₀) 1 0 = 0 := by
    show (!![algebraMap R K₀ ϖ ^ k, a₀; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0; simp
  have h11 : (chartMat (K₀ := K₀) hϖ k a₀ : GL (Fin 2) K₀) 1 1 = 1 := by
    show (!![algebraMap R K₀ ϖ ^ k, a₀; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1; simp
  have h00 : (chartMat (K₀ := K₀) hϖ k a₀ : GL (Fin 2) K₀) 0 0 = algebraMap R K₀ ϖ ^ k := by
    show (!![algebraMap R K₀ ϖ ^ k, a₀; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 0 0 = _; simp
  have h01 : (chartMat (K₀ := K₀) hϖ k a₀ : GL (Fin 2) K₀) 0 1 = a₀ := by
    show (!![algebraMap R K₀ ϖ ^ k, a₀; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 0 1 = _; simp
  rw [pmoebius_mk K₀ _ y (moebius_denom_ne_zero_of_mem K₀ hy _), moebius, h10, h11, h00, h01, map_zero, map_one,
    zero_mul, zero_add, div_one]

end Geometry

end UAdj

open UAdj in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ₁)
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (z : ↥(upperHalfPlane K₀ K)) :
    ∃ (g g' : GL (Fin 2) K₀) (w w' : K) (y y' : ↥(upperHalfPlane K₀ K)),
      w ∈ affinoid ϖ₁ 0 ∧ w' ∈ affinoid ϖ₁ 0 ∧
      (y : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w ∧
      (y' : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w' ∧
      (CerednikDrinfeld.BruhatTits.tree R K₀).Adj (g • LT.LatticeTree.stdVertex R K₀)
        (g' • LT.LatticeTree.stdVertex R K₀) ∧
      min (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y)) (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y')) ≤
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ∧
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≤
        max (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y)) (Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y')) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hpdef
  have hp0 : 0 < p := p_pos hϖ
  have hp1 : p < 1 := p_lt_one hϖ hint ϖ₁
  have hΩ0 : affinoid ϖ₁ 0 ⊆ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0
  obtain ⟨ω, hω⟩ := exists_mem_affinoid_zero hϖ hint hv ϖ₁
  obtain ⟨k, a₀, y, hzy, hdich⟩ := exists_chart hϖ hint ϖ₁ hex z.2
  set gA : GL (Fin 2) K₀ := chartMat (K₀ := K₀) hϖ k a₀ with hgAdef
  set D : GL (Fin 2) K₀ := dMat K₀ hϖ with hDdef
  set v₀ := LT.LatticeTree.stdVertex R K₀ with hv₀

  have hyΩ : y ∈ upperHalfPlane K₀ K := by
    rw [mem_upperHalfPlane_iff]
    intro b hb
    have hz := (mem_upperHalfPlane_iff K₀ (z : K)).1 z.2 (algebraMap R K₀ ϖ ^ k * b + a₀)
    apply hz
    rw [map_add, map_mul, hb, ← hzy]
  have hgA : ∀ x : K, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) x = algebraMap K₀ K (algebraMap R K₀ ϖ ^ k) * x + algebraMap K₀ K a₀ :=
    fun x hx => pmoebius_chartMat hϖ k a₀ hx
  have hD : ∀ x : K, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (Matrix.ProjGenLinGroup.mk D⁻¹) x = algebraMap K₀ K (algebraMap R K₀ ϖ) * x :=
    fun x hx => pmoebius_dMat_inv hϖ hx
  have hadj : (BruhatTits.tree R K₀).Adj (gA • v₀) ((gA * D⁻¹) • v₀) := by
    rw [mul_smul]
    exact Mumford.GraphAction.smul_adj gA (adj_stdVertex_dMat_inv_smul hϖ)

  let y'pt : ↥(upperHalfPlane K₀ K) :=
    ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk (gA * D⁻¹)) ω, pmoebius_mem_upperHalfPlane K₀ (hΩ0 hω) _⟩
  have hy'pt : (y'pt : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) (algebraMap K₀ K (algebraMap R K₀ ϖ) * ω) := by
    show pmoebius K₀ (Matrix.ProjGenLinGroup.mk (gA * D⁻¹)) ω = _
    rw [map_mul, pmoebius_mul K₀ (hΩ0 hω), hD ω (hΩ0 hω)]
  rcases hdich with ⟨hy1, hyall⟩ | ⟨hpy, hy1⟩
  ·
    have hyaff : y ∈ affinoid ϖ₁ 0 :=
      (mem_affinoid_iff' ϖ₁ 0 y).2 ⟨by rw [pow_zero]; exact hy1.le, fun b => by rw [pow_zero]; exact hyall b⟩
    refine ⟨gA, gA * D⁻¹, y, ω, z, y'pt, hyaff, hω, ?_, rfl, hadj, min_le_left _ _, le_max_left _ _⟩
    rw [hgA y hyΩ]; exact hzy
  ·
    let ypt : ↥(upperHalfPlane K₀ K) :=
      ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) ω, pmoebius_mem_upperHalfPlane K₀ (hΩ0 hω) _⟩
    refine ⟨gA, gA * D⁻¹, ω, ω, ypt, y'pt, hω, hω, rfl, rfl, hadj, ?_⟩

    set F : ↥(holRing ϖ₁) := (Matrix.ProjGenLinGroup.mk gA)⁻¹ • f with hFdef
    have hFunit : IsUnit F := by
      have := hf.map (MulSemiringAction.toRingHom _ ↥(holRing ϖ₁) (Matrix.ProjGenLinGroup.mk gA)⁻¹)
      rwa [MulSemiringAction.toRingHom_apply] at this
    have hFapp : ∀ (x : K) (hx : x ∈ upperHalfPlane K₀ K),
        (F : ↥(upperHalfPlane K₀ K) → K) ⟨x, hx⟩ =
          (f : ↥(upperHalfPlane K₀ K) → K)
            ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) x, pmoebius_mem_upperHalfPlane K₀ hx _⟩ := by
      intro x hx
      rw [hFdef, coe_smul_holRing_apply, inv_inv]
      rfl
    obtain ⟨CP, CQ, mP, mQ, hCP, hCQ, hlaw⟩ := exists_monomial_law hϖ hint ϖ₁ F hFunit
    have hωB : ω ∈ edgeRegion K₀ (K := K) p := mem_edgeRegion_of_mem_affinoid_zero ϖ₁ p hω
    have hϖωB : algebraMap K₀ K (algebraMap R K₀ ϖ) * ω ∈ edgeRegion K₀ (K := K) p := smul_mem_edgeRegion hϖ ϖ₁ hω
    have hyB : y ∈ edgeRegion K₀ (K := K) p := Or.inr (Or.inl ⟨hpy, hy1⟩)
    have hvω : Valued.v ω = 1 := by
      have h := (mem_affinoid_iff' ϖ₁ 0 ω).1 hω
      simp only [pow_zero] at h
      exact le_antisymm h.1 (by simpa using h.2 0)
    have hvϖω : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ) * ω) = p := by
      rw [Valuation.map_mul, hvω, mul_one]
    have ha := hlaw ω hωB
    have hb := hlaw _ hϖωB
    have hc := hlaw y hyB
    rw [hFapp, hvω] at ha
    rw [hFapp, hvϖω] at hb
    rw [hFapp] at hc

    have e1 : (f : ↥(upperHalfPlane K₀ K) → K) z =
        (f : ↥(upperHalfPlane K₀ K) → K)
          ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) y, pmoebius_mem_upperHalfPlane K₀ hyΩ _⟩ :=
      congrArg _ (Subtype.ext (show (z : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) y by
        rw [hgA y hyΩ]; exact hzy))
    have e2 : (f : ↥(upperHalfPlane K₀ K) → K) y'pt =
        (f : ↥(upperHalfPlane K₀ K) → K)
          ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk gA) (algebraMap K₀ K (algebraMap R K₀ ϖ) * ω),
            pmoebius_mem_upperHalfPlane K₀ (edgeRegion_subset_upperHalfPlane hϖ hint ϖ₁ hϖωB) _⟩ :=
      congrArg _ (Subtype.ext hy'pt)
    rw [e1, e2]
    have hpp : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) = p := rfl
    exact between_of_monomial_law hp0 hp1 hCP hCQ (by simpa using ha) hb hc hpy hy1

end

end S_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit (solution)
