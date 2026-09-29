-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4968b6e5-eba9-53fe-bd2d-bc9f50b3d48d

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Filter CerednikDrinfeld.Omega

namespace IdAnn

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

variable [IsAlgClosed K]

theorem eq_C_mul_prod (P : K[X]) : P = C P.leadingCoeff * (P.roots.map fun α => X - C α).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((splits_iff_card_roots.1 (IsAlgClosed.splits P)).symm ▸ rfl)).symm

theorem exists_generic (B : Multiset K) : ∃ y : K, v y ≤ 1 ∧ ∀ b ∈ B, v b ≤ 1 → 1 ≤ v (y - b) := by
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

end IdAnn

namespace Z1

open IdAnn Polynomial CerednikDrinfeld.Omega

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem v_sub_eq_of_lt {x y : K} (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg]; apply Valuation.map_add_eq_of_lt_left; rwa [Valuation.map_neg]

theorem v_sub_comm (x y : K) : v (x - y) = v (y - x) := Valuation.map_sub_swap _ x y

theorem v_eq_of_v_sub_lt {a b : K} (h : v (a - b) < v b) : v a = v b := by
  have e : a = b + (a - b) := by ring
  rw [e]; exact Valuation.map_add_eq_of_lt_left _ h

def InF (c π : K) (Z : Finset K) (z : K) : Prop := v (z - c) ≤ v π ∧ ∀ ζ ∈ Z, v π ≤ v (z - ζ)

theorem inF_of_v_sub_lt {c π : K} {Z : Finset K} {z w : K} (hz : InF c π Z z) (hw : v (w - z) < v π) : InF c π Z w := by
  refine ⟨?_, fun ζ hζ => ?_⟩
  · have e : w - c = (w - z) + (z - c) := by ring
    rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hw.le hz.1)
  · have h1 := hz.2 ζ hζ
    have e : w - ζ = (z - ζ) - (z - w) := by ring
    rw [e, v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact hw.trans_le h1)]
    exact h1

theorem v_sub_le_of_not_lt {c α z w : K} {ρ : Γ₀} (hz : v (z - c) ≤ ρ) (hzα : ¬ v (z - α) < ρ) (hw : v (w - c) ≤ ρ) :
    v (w - α) ≤ v (z - α) := by
  rw [not_lt] at hzα
  rcases le_or_gt (v (α - c)) ρ with hα | hα
  · have e : w - α = (w - c) - (α - c) := by ring
    rw [e]; exact ((Valuation.map_sub _ _ _).trans (max_le hw hα)).trans hzα
  · have e1 : v (w - α) = v (α - c) := by
      have e : w - α = (w - c) - (α - c) := by ring
      rw [e, Valuation.map_sub_swap, v_sub_eq_of_lt (hw.trans_lt hα)]
    have e2 : v (z - α) = v (α - c) := by
      have e : z - α = (z - c) - (α - c) := by ring
      rw [e, Valuation.map_sub_swap, v_sub_eq_of_lt (hz.trans_lt hα)]
    rw [e1, e2]

variable [IsAlgClosed K]

theorem v_eval_le_of_generic (P : K[X]) {c z w : K} {ρ : Γ₀} (hz : v (z - c) ≤ ρ)
    (hgen : ∀ α ∈ P.roots, ¬ v (z - α) < ρ) (hw : v (w - c) ≤ ρ) :
    v (P.eval w) ≤ v (P.eval z) := by
  conv_lhs => rw [eq_C_mul_prod P]
  conv_rhs => rw [eq_C_mul_prod P]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
  refine mul_le_mul' le_rfl (Multiset.prod_map_le_prod_map _ _ fun α hα => ?_)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  exact v_sub_le_of_not_lt hz (hgen α hα) hw

theorem v_eval_eq_of_generic (P : K[X]) {c z w : K} {ρ : Γ₀} (hz : v (z - c) ≤ ρ)
    (hgz : ∀ α ∈ P.roots, ¬ v (z - α) < ρ) (hw : v (w - c) ≤ ρ) (hgw : ∀ α ∈ P.roots, ¬ v (w - α) < ρ) :
    v (P.eval w) = v (P.eval z) :=
  le_antisymm (v_eval_le_of_generic P hz hgz hw) (v_eval_le_of_generic P hw hgw hz)

theorem exists_generic_disc (c π : K) (hπ : π ≠ 0) (B : Multiset K) :
    ∃ y : K, v (y - c) ≤ v π ∧ ∀ b ∈ B, v π ≤ v (y - b) := by
  have hvπ : 0 < v π := (Valuation.pos_iff _).mpr hπ
  obtain ⟨y', hy', hgen⟩ := exists_generic (B.map fun b => (b - c) / π)
  refine ⟨π * y' + c, ?_, fun b hb => ?_⟩
  · rw [add_sub_cancel_right, map_mul]
    calc v π * v y' ≤ v π * 1 := mul_le_mul' le_rfl hy'
      _ = v π := mul_one _
  · have e : π * y' + c - b = π * (y' - (b - c) / π) := by
      rw [mul_sub, mul_div_cancel₀ _ hπ]; ring
    rw [e, map_mul]
    have hmem : (b - c) / π ∈ B.map fun b => (b - c) / π := Multiset.mem_map_of_mem _ hb
    rcases le_or_gt (v ((b - c) / π)) 1 with h1 | h1
    · exact le_mul_of_one_le_right' (hgen _ hmem h1)
    · have : v (y' - (b - c) / π) = v ((b - c) / π) := by
        rw [Valuation.map_sub_swap, v_sub_eq_of_lt (hy'.trans_lt h1)]
      rw [this]
      exact le_mul_of_one_le_right' h1.le

end Z1

namespace Z2

open IdAnn Polynomial CerednikDrinfeld.Omega

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem eq_zero_of_forall_v_lt {x : K} (h : ∀ e : K, e ≠ 0 → v x < v e) : x = 0 := by
  by_contra hx; exact lt_irrefl _ (h x hx)

theorem v_sub_eq_max {c α y : K} (h : ¬ v (y - α) < v (y - c)) : v (y - α) = max (v (y - c)) (v (α - c)) := by
  rw [not_lt] at h
  have e : y - α = (y - c) - (α - c) := by ring
  rcases lt_trichotomy (v (α - c)) (v (y - c)) with hlt | heq | hgt
  · rw [max_eq_left hlt.le, e, Z1.v_sub_eq_of_lt hlt]
  · rw [heq, max_self]
    refine le_antisymm ?_ h
    rw [e]; exact (Valuation.map_sub _ _ _).trans (by rw [heq, max_self])
  · rw [max_eq_right hgt.le, e, Valuation.map_sub_swap, Z1.v_sub_eq_of_lt hgt]

theorem not_lt_of_v_ne {c α y : K} (h : v (α - c) ≠ v (y - c)) : ¬ v (y - α) < v (y - c) := by
  intro hlt
  apply h
  have e : α - c = (y - c) - (y - α) := by ring
  rw [e, Z1.v_sub_eq_of_lt hlt]

section AlgClosed
variable [IsAlgClosed K]

theorem v_eval_eq_prod_max (P : K[X]) {c y : K} (hgen : ∀ α ∈ P.roots, ¬ v (y - α) < v (y - c)) :
    v (P.eval y) = v P.leadingCoeff * (P.roots.map fun α => max (v (y - c)) (v (α - c))).prod := by
  conv_lhs => rw [eq_C_mul_prod P]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => ?_)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  exact v_sub_eq_max (hgen α hα)

theorem exists_generic_circle (c π : K) (hπ : π ≠ 0) (B : Multiset K) :
    ∃ y : K, v (y - c) = v π ∧ ∀ b ∈ B, v π ≤ v (y - b) := by
  obtain ⟨y, hyc, hgen⟩ := Z1.exists_generic_disc c π hπ (c ::ₘ B)
  exact ⟨y, le_antisymm hyc (hgen c (Multiset.mem_cons_self _ _)), fun b hb => hgen b (Multiset.mem_cons_of_mem hb)⟩

end AlgClosed

theorem root_not_interior {S : Set K} {c πd πs : K} {Z Ξ : Finset K}
    (hZ : ∀ ζ ∈ Z, v πd ≤ v (c - ζ)) (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs)
    (hS : ∀ z : K, v πs ≤ v (z - c) → v (z - c) ≤ v πd →
      (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) → (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) → z ∈ S)
    {Q : K[X]} (hQ : ∀ z ∈ S, Q.eval z ≠ 0) (hQ0 : Q ≠ 0) {β : K} (hβ : β ∈ Q.roots) :
    v (β - c) ≤ v πs ∨ v πd ≤ v (β - c) := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hβS : β ∈ S := by
    refine hS β h1.le h2.le (fun ζ hζ => ?_) (fun ξ hξ => ?_)
    · have e : β - ζ = (c - ζ) - (c - β) := by ring
      rw [e, Z1.v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact h2.trans_le (hZ ζ hζ))]
      exact hZ ζ hζ
    · have e : β - ξ = (β - c) - (ξ - c) := by ring
      rw [e, Z1.v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact (hΞ ξ hξ).trans_lt h1)]
      exact h1.le
  exact hQ β hβS ((mem_roots hQ0).1 hβ)

theorem max_mul_max_le {ρ ρ' ρm a : Γ₀} (h : ρm * ρm = ρ * ρ') :
    max ρm a * max ρm a ≤ max ρ a * max ρ' a := by
  rcases le_total ρm a with h1 | h1
  · rw [max_eq_right h1]; exact mul_le_mul' (le_max_right _ _) (le_max_right _ _)
  · rw [max_eq_left h1, h]; exact mul_le_mul' (le_max_left _ _) (le_max_left _ _)

theorem max_mul_max_eq {ρ ρ' ρm a s d : Γ₀} (h : ρm * ρm = ρ * ρ')
    (hρ : s ≤ ρ) (hρd : ρ ≤ d) (hρ' : s ≤ ρ') (hρ'd : ρ' ≤ d) (hm : s ≤ ρm) (hmd : ρm ≤ d)
    (ha : a ≤ s ∨ d ≤ a) :
    max ρm a * max ρm a = max ρ a * max ρ' a := by
  rcases ha with ha | ha
  · rw [max_eq_left (ha.trans hm), max_eq_left (ha.trans hρ), max_eq_left (ha.trans hρ'), h]
  · rw [max_eq_right (hmd.trans ha), max_eq_right (hρd.trans ha), max_eq_right (hρ'd.trans ha)]

theorem prod_max_mul_le (R : Multiset K) (c : K) {ρ ρ' ρm : Γ₀} (h : ρm * ρm = ρ * ρ') :
    (R.map fun α => max ρm (v (α - c))).prod * (R.map fun α => max ρm (v (α - c))).prod ≤
      (R.map fun α => max ρ (v (α - c))).prod * (R.map fun α => max ρ' (v (α - c))).prod := by
  rw [← Multiset.prod_map_mul, ← Multiset.prod_map_mul]
  exact Multiset.prod_map_le_prod_map _ _ fun α _ => max_mul_max_le h

theorem prod_max_mul_eq (R : Multiset K) (c : K) {ρ ρ' ρm s d : Γ₀} (h : ρm * ρm = ρ * ρ')
    (hρ : s ≤ ρ) (hρd : ρ ≤ d) (hρ' : s ≤ ρ') (hρ'd : ρ' ≤ d) (hm : s ≤ ρm) (hmd : ρm ≤ d)
    (hR : ∀ α ∈ R, v (α - c) ≤ s ∨ d ≤ v (α - c)) :
    (R.map fun α => max ρm (v (α - c))).prod * (R.map fun α => max ρm (v (α - c))).prod =
      (R.map fun α => max ρ (v (α - c))).prod * (R.map fun α => max ρ' (v (α - c))).prod := by
  rw [← Multiset.prod_map_mul, ← Multiset.prod_map_mul]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => max_mul_max_eq h hρ hρd hρ' hρ'd hm hmd (hR α hα))

end Z2

namespace Z2

open IdAnn Polynomial CerednikDrinfeld.Omega

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def InA (c πd πs : K) (Z Ξ : Finset K) (z : K) : Prop :=
  v πs ≤ v (z - c) ∧ v (z - c) ≤ v πd ∧ (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) ∧ ∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)

theorem zcond_of_lt {c πd : K} {Z : Finset K} (hZ : ∀ ζ ∈ Z, v πd ≤ v (c - ζ)) {z : K} (hz : v (z - c) < v πd) :
    ∀ ζ ∈ Z, v πd ≤ v (z - ζ) := by
  intro ζ hζ
  have e : z - ζ = (c - ζ) - (c - z) := by ring
  rw [e, Z1.v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact hz.trans_le (hZ ζ hζ))]
  exact hZ ζ hζ

theorem xcond_of_lt {c πs : K} {Ξ : Finset K} (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs) {z : K} (hz : v πs < v (z - c)) :
    ∀ ξ ∈ Ξ, v πs ≤ v (z - ξ) := by
  intro ξ hξ
  have e : z - ξ = (z - c) - (ξ - c) := by ring
  rw [e, Z1.v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact (hΞ ξ hξ).trans_lt hz)]
  exact hz.le

end Z2

namespace Z2

open IdAnn Polynomial CerednikDrinfeld.Omega

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem inA_of_v_sub_lt {c πd πs : K} {Z Ξ : Finset K} (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs)
    {z w : K} (hz : InA c πd πs Z Ξ z) (hw : v (z - w) < v (z - c)) : InA c πd πs Z Ξ w := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hwc : v (w - c) = v (z - c) := by
    have e : w - c = (z - c) - (z - w) := by ring
    rw [e, Z1.v_sub_eq_of_lt hw]
  refine ⟨hwc ▸ h1, hwc ▸ h2, fun ζ hζ => ?_, fun ξ hξ => ?_⟩
  · have e : w - ζ = (z - ζ) - (z - w) := by ring
    rw [e, Z1.v_sub_eq_of_lt (hw.trans_le (h2.trans (h3 ζ hζ)))]; exact h3 ζ hζ
  ·
    have hzξ : v (z - c) ≤ v (z - ξ) := by
      rcases eq_or_lt_of_le h1 with heq | hlt
      · rw [← heq]; exact h4 ξ hξ
      · have e : z - ξ = (z - c) - (ξ - c) := by ring
        rw [e, Z1.v_sub_eq_of_lt (x := z - c) (y := ξ - c) (by rw [Z1.v_sub_comm ξ c]; exact (hΞ ξ hξ).trans_lt hlt)]
    have e : w - ξ = (z - ξ) - (z - w) := by ring
    rw [e, Z1.v_sub_eq_of_lt (hw.trans_le hzξ)]; exact h4 ξ hξ

theorem den_generic {S : Set K} {c πd πs : K} {Z Ξ : Finset K} (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs)
    (hS : ∀ z : K, v πs ≤ v (z - c) → v (z - c) ≤ v πd →
      (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) → (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) → z ∈ S)
    {Q : K[X]} (hQ : ∀ z ∈ S, Q.eval z ≠ 0) (hQ0 : Q ≠ 0) {z : K} (hz : InA c πd πs Z Ξ z) :
    ∀ β ∈ Q.roots, ¬ v (z - β) < v (z - c) := by
  intro β hβ hlt
  have hβA := inA_of_v_sub_lt hΞ hz hlt
  exact hQ β (hS β hβA.1 hβA.2.1 hβA.2.2.1 hβA.2.2.2) ((mem_roots hQ0).1 hβ)

theorem inA_of_generic {c πd πs : K} {Z Ξ : Finset K} (hZ : ∀ ζ ∈ Z, v πd ≤ v (c - ζ)) (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs)
    {τ y : K} (hyc : v (y - c) = v τ) (hsτ : v πs ≤ v τ) (hτd : v τ ≤ v πd)
    (hgen : ∀ b ∈ Z.val + Ξ.val, v τ ≤ v (y - b)) : InA c πd πs Z Ξ y := by
  refine ⟨hyc ▸ hsτ, hyc ▸ hτd, fun ζ hζ => ?_, fun ξ hξ => ?_⟩
  · rcases eq_or_lt_of_le hτd with h | h
    · rw [← h]; exact hgen ζ (Multiset.mem_add.mpr (Or.inl hζ))
    · exact zcond_of_lt hZ (by rw [hyc]; exact h) ζ hζ
  · rcases eq_or_lt_of_le hsτ with h | h
    · rw [h]; exact hgen ξ (Multiset.mem_add.mpr (Or.inr hξ))
    · exact xcond_of_lt hΞ (by rw [hyc]; exact h) ξ hξ

end Z2
namespace CoverDrv

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem v_sub_le_max (a b c₁ : K) : v (a - c₁) ≤ max (v (a - b)) (v (b - c₁)) := by
  have : a - c₁ = (a - b) + (b - c₁) := by ring
  rw [this]; exact Valuation.map_add _ _ _

private theorem _root_.CoverDrv.v_sub_eq_of_lt {a b c₁ : K} (h : v (a - b) < v (b - c₁)) : v (a - c₁) = v (b - c₁) := by
  have : a - c₁ = (a - b) + (b - c₁) := by ring
  rw [this, Valuation.map_add_eq_of_lt_right _ h]

p2m_export "CoverDrv" "v_sub_eq_of_lt"
theorem v_sub_eq_of_lt' {a b c₁ : K} (h : v (b - c₁) < v (a - b)) : v (a - c₁) = v (a - b) := by
  have : a - c₁ = (a - b) + (b - c₁) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ h]

section Generic
variable [IsAlgClosed K]

theorem exists_generic (B : Multiset K) : ∃ y : K, v y ≤ 1 ∧ ∀ b ∈ B, v b ≤ 1 → 1 ≤ v (y - b) := by
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

private theorem _root_.CoverDrv.exists_generic_disc (x π : K) (hπ : π ≠ 0) (B : Multiset K) :
    ∃ y : K, v (y - x) ≤ v π ∧ ∀ b ∈ B, v π ≤ v (y - b) := by
  have hvπ : 0 < v π := (Valuation.pos_iff _).mpr hπ
  obtain ⟨y', hy', hgen⟩ := exists_generic (B.map fun b => (b - x) / π)
  refine ⟨π * y' + x, ?_, fun b hb => ?_⟩
  · rw [add_sub_cancel_right, map_mul]
    calc v π * v y' ≤ v π * 1 := mul_le_mul' le_rfl hy'
      _ = v π := mul_one _
  · have e : π * y' + x - b = π * (y' - (b - x) / π) := by
      rw [mul_sub, mul_div_cancel₀ _ hπ]; ring
    rw [e, map_mul]
    have hmem : (b - x) / π ∈ B.map fun b => (b - x) / π := Multiset.mem_map_of_mem _ hb
    rcases le_or_gt (v ((b - x) / π)) 1 with h1 | h1
    · exact le_mul_of_one_le_right' (hgen _ hmem h1)
    · have : v (y' - (b - x) / π) = v ((b - x) / π) := by
        rw [Valuation.map_sub_swap]
        have e2 : (b - x) / π - y' = ((b - x) / π - 0) - (y' - 0) := by ring
        rw [sub_zero] at *
        exact Valuation.map_sub_eq_of_lt_left _ (by simpa using hy'.trans_lt h1)
      rw [this]
      exact le_mul_of_one_le_right' h1.le

p2m_export "CoverDrv" "exists_generic_disc"
end Generic

structure CData (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] where
  S : Set K
  T : Finset K
  ρ : K → K
  c : K
  R₀ : K
  hR₀ : R₀ ≠ 0
  hρ : ∀ t ∈ T, ρ t ≠ 0
  hS : ∀ z : K, z ∈ S ↔ Valued.v (z - c) ≤ Valued.v R₀ ∧ ∀ t ∈ T, Valued.v (ρ t) ≤ Valued.v (z - t)
  hc : c ∈ S
  P : Set K → Prop
  P_mono : ∀ {A B : Set K}, A ⊆ B → P B → P A
  P_union : ∀ {A B : Set K}, P A → P B → P (A ∪ B)
  P_empty : P ∅
  discP : ∀ (x π : K), π ≠ 0 → ∀ (Z : Finset K), (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (x - ζ)) →
    (∀ z : K, Valued.v (z - x) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S) →
    P {z | Valued.v (z - x) ≤ Valued.v π ∧ ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)}
  annP : ∀ (x πd πs : K), πd ≠ 0 → πs ≠ 0 → Valued.v πs < Valued.v πd →
    ∀ (Z : Finset K), (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (x - ζ)) →
    ∀ (Ξ : Finset K), (∀ ξ ∈ Ξ, Valued.v (x - ξ) ≤ Valued.v πs) →
    (∀ z : K, Valued.v πs ≤ Valued.v (z - x) → Valued.v (z - x) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → z ∈ S) →
    P {z | Valued.v πs ≤ Valued.v (z - x) ∧ Valued.v (z - x) ≤ Valued.v πd ∧
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) ∧ ∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)}

namespace CData

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (d : CData K)

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))
local notation "R" => Valued.v (CData.R₀ d)

theorem P_of_forall_not {A : Set K} (h : ∀ z, z ∉ A) : d.P A :=
  d.P_mono (fun z hz => absurd hz (h z)) d.P_empty

theorem P_biUnion {ι : Type} (F : Finset ι) (A : ι → Set K) (h : ∀ i ∈ F, d.P (A i)) : d.P (⋃ i ∈ F, A i) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact d.P_of_forall_not fun z hz => by simp at hz
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact d.P_union (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem vρ_pos {t : K} (ht : t ∈ d.T) : 0 < v (d.ρ t) := (Valuation.pos_iff _).2 (d.hρ t ht)

theorem ρ_le_c {t : K} (ht : t ∈ d.T) : v (d.ρ t) ≤ v (d.c - t) := ((d.hS d.c).1 d.hc).2 t ht

theorem notMem_of_hole {z t : K} (ht : t ∈ d.T) (h : v (z - t) < v (d.ρ t)) : z ∉ d.S := fun hz =>
  (((d.hS z).1 hz).2 t ht).not_gt h

def Hol (x : K) (η : Γ₀) : Finset K := d.T.filter fun t => v (t - x) ≤ η

theorem mem_Hol {x : K} {η : Γ₀} {t : K} : t ∈ d.Hol x η ↔ t ∈ d.T ∧ v (t - x) ≤ η := Finset.mem_filter

def gen (x : K) (η : Γ₀) : Set K := {z | v (z - x) ≤ η ∧ ∀ t ∈ d.Hol x η, η ≤ v (z - t)}

def Clean (x : K) (η : Γ₀) : Prop :=
  ∀ t ∈ d.T, (v (t - x) ≤ η → v (d.ρ t) ≤ η) ∧ (η < v (t - x) → v (d.ρ t) ≤ v (t - x))

theorem forall_notMem_of_not_clean {x : K} {η : Γ₀} (h : ¬ d.Clean x η) :
    ∀ z, z ∈ d.S ∩ {z | v (z - x) ≤ η} → False := by
  rintro z ⟨hz, hzx : v (z - x) ≤ η⟩
  simp only [Clean, not_forall, not_and_or, not_le, exists_prop] at h
  obtain ⟨t, ht, h⟩ := h
  refine d.notMem_of_hole ht ?_ hz
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc v (z - t) = v ((z - x) - (t - x)) := by ring_nf
      _ ≤ max (v (z - x)) (v (t - x)) := Valuation.map_sub _ _ _
      _ ≤ η := max_le hzx h1
      _ < v (d.ρ t) := h2
  · have hlt : v (z - x) < v (t - x) := hzx.trans_lt h1
    calc v (z - t) = v ((z - x) - (t - x)) := by ring_nf
      _ = v (t - x) := Valuation.map_sub_eq_of_lt_right _ hlt
      _ < v (d.ρ t) := h2

theorem memS_of {x : K} {η : Γ₀} (hx : v (x - d.c) ≤ R) (hη : η ≤ R) (hcl : d.Clean x η) {z : K}
    (hz : v (z - x) ≤ η) (hholes : ∀ t ∈ d.Hol x η, v (d.ρ t) ≤ v (z - t)) : z ∈ d.S := by
  refine (d.hS z).2 ⟨?_, fun t ht => ?_⟩
  · calc v (z - d.c) = v ((z - x) + (x - d.c)) := by ring_nf
      _ ≤ max (v (z - x)) (v (x - d.c)) := Valuation.map_add _ _ _
      _ ≤ R := max_le (hz.trans hη) hx
  · by_cases htx : v (t - x) ≤ η
    · exact hholes t (d.mem_Hol.2 ⟨ht, htx⟩)
    · push Not at htx
      have hlt : v (z - x) < v (t - x) := hz.trans_lt htx
      calc v (d.ρ t) ≤ v (t - x) := (hcl t ht).2 htx
        _ = v (z - t) := by
          rw [← Valuation.map_sub_eq_of_lt_right _ hlt]; ring_nf

theorem gen_subset_S {x : K} {η : Γ₀} (hx : v (x - d.c) ≤ R) (hη : η ≤ R) (hcl : d.Clean x η) :
    d.gen x η ⊆ d.S := fun z hz =>
  d.memS_of hx hη hcl hz.1 fun t ht => ((hcl t (d.mem_Hol.1 ht).1).1 (d.mem_Hol.1 ht).2).trans (hz.2 t ht)

open scoped Classical in
def μ (x : K) (η : Γ₀) : ℕ :=
  2 * (d.Hol x η).card + if ∃ t₁ ∈ d.Hol x η, ∀ t ∈ d.Hol x η, v (t - t₁) < η then 1 else 0

theorem cover (x : K) (η : Γ₀) :
    d.S ∩ {z | v (z - x) ≤ η} ⊆ d.gen x η ∪ ⋃ t ∈ d.Hol x η, (d.S ∩ {z | v (z - t) < η}) := by
  rintro z ⟨hzS, hzx : v (z - x) ≤ η⟩
  by_cases h : ∀ t ∈ d.Hol x η, η ≤ v (z - t)
  · exact Or.inl ⟨hzx, h⟩
  · push Not at h
    obtain ⟨t, ht, hlt⟩ := h
    exact Or.inr (Set.mem_iUnion₂.2 ⟨t, ht, hzS, hlt⟩)

end CData

end CoverDrv

namespace CoverDrv

open scoped Classical

namespace CData

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
variable (d : CData K)

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))
local notation "R" => Valued.v (CData.R₀ d)

omit [IsAlgClosed K] in
theorem v_sub_le_max₃ (a b c₁ : K) : v (a - c₁) ≤ max (max (v (a - b)) (v (b - c₁))) (v (a - b)) := by
  exact (v_sub_le_max a b c₁).trans (le_max_left _ _)

theorem P_gen {x πη : K} (hπη : πη ≠ 0) (hx : v (x - d.c) ≤ R) (hη : v πη ≤ R) (hcl : d.Clean x (v πη)) :
    d.P (d.gen x (v πη)) := by
  obtain ⟨x', hx'x, hx'gen⟩ := exists_generic_disc x πη hπη (d.Hol x (v πη)).val
  have hsub : ∀ z : K, v (z - x') ≤ v πη → (∀ t ∈ d.Hol x (v πη), v πη ≤ v (z - t)) → z ∈ d.gen x (v πη) :=
    fun z h1 h2 => ⟨(v_sub_le_max z x' x).trans (max_le h1 hx'x), h2⟩
  have h := d.discP x' πη hπη (d.Hol x (v πη)) (fun t ht => hx'gen t ht)
    (fun z h1 h2 => d.gen_subset_S hx hη hcl (hsub z h1 h2))
  refine d.P_mono (fun z hz => ?_) h
  exact ⟨(v_sub_le_max z x x').trans (max_le hz.1 (by rw [Valuation.map_sub_swap]; exact hx'x)), hz.2⟩

theorem class_step (n : ℕ)
    (IH : ∀ m < n, ∀ (x πη : K), πη ≠ 0 → d.μ x (v πη) ≤ m → v (x - d.c) ≤ R → v πη ≤ R →
      d.P (d.S ∩ {z | v (z - x) ≤ v πη}))
    (x πη t₁ : K) (hπη : πη ≠ 0) (hμ : d.μ x (v πη) ≤ n) (hx : v (x - d.c) ≤ R) (hη : v πη ≤ R)
    (hcl : d.Clean x (v πη)) (ht₁ : t₁ ∈ d.Hol x (v πη)) :
    d.P (d.S ∩ {z | v (z - t₁) < v πη}) := by
  set η := v πη with hηdef
  have hηpos : 0 < η := (Valuation.pos_iff _).2 hπη
  obtain ⟨ht₁T, ht₁x⟩ := d.mem_Hol.1 ht₁
  have hxt : ∀ z, v (z - t₁) ≤ η ↔ v (z - x) ≤ η := fun z =>
    ⟨fun h => (v_sub_le_max z t₁ x).trans (max_le h ht₁x),
     fun h => (v_sub_le_max z x t₁).trans (max_le h (by rw [Valuation.map_sub_swap]; exact ht₁x))⟩
  have ht₁c : v (t₁ - d.c) ≤ R := (v_sub_le_max t₁ x d.c).trans (max_le (ht₁x.trans hη) hx)

  set HolU := (d.Hol x η).filter fun t => v (t - t₁) < η with hHolU
  have memU : ∀ {t}, t ∈ HolU ↔ t ∈ d.Hol x η ∧ v (t - t₁) < η := fun {t} => Finset.mem_filter
  have ht₁U : t₁ ∈ HolU := memU.2 ⟨ht₁, by rw [sub_self, map_zero]; exact hηpos⟩
  set cand : Finset K := HolU.image (fun t => t - t₁) ∪ HolU.image d.ρ with hcand
  have hcandne : cand.Nonempty := ⟨d.ρ t₁, Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht₁U)⟩
  obtain ⟨πs, hπs_mem, hπs_max⟩ := Finset.exists_max_image cand (fun q => v q) hcandne
  set s := v πs with hsdef
  have hsU : ∀ t ∈ HolU, v (t - t₁) ≤ s ∧ v (d.ρ t) ≤ s := fun t ht =>
    ⟨hπs_max _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht)),
     hπs_max _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))⟩
  have hs_pos : 0 < s := (d.vρ_pos ht₁T).trans_le (hsU t₁ ht₁U).2
  have hπs0 : πs ≠ 0 := (Valuation.pos_iff _).1 hs_pos
  have memU_T : ∀ {t}, t ∈ HolU → t ∈ d.T := fun ht => (d.mem_Hol.1 (memU.1 ht).1).1
  have hs_le : s ≤ η := by
    rcases Finset.mem_union.1 hπs_mem with h | h
    · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
      rw [hsdef, ← hteq]; exact (memU.1 ht).2.le
    · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
      rw [hsdef, ← hteq]; exact (hcl t (memU_T ht)).1 (d.mem_Hol.1 (memU.1 ht).1).2

  have hdiff : ∀ t' ∈ HolU, πs = t' - t₁ → ∀ t₂ ∈ HolU, ¬ ∀ t ∈ HolU, v (t - t₂) < s := by
    intro t' ht' hπ t₂ ht₂ hall
    have h1 := hall t' ht'
    have h2 := hall t₁ ht₁U
    have : v (t' - t₁) < s := (v_sub_le_max t' t₂ t₁).trans_lt (max_lt h1 (by rw [Valuation.map_sub_swap]; exact h2))
    rw [← hπ] at this
    exact this.ne rfl
  rcases hs_le.eq_or_lt with hs_eq | hs_lt
  ·
    have hex : ∃ t' ∈ HolU, v (d.ρ t') = η := by
      rcases Finset.mem_union.1 hπs_mem with h | h
      · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
        exact absurd ((memU.1 ht).2.trans_eq hs_eq.symm) (by rw [hsdef, ← hteq]; exact lt_irrefl _)
      · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
        exact ⟨t, ht, by rw [hteq]; exact hs_eq⟩
    obtain ⟨t', ht'U, hρt'⟩ := hex
    refine d.P_of_forall_not fun z hz => ?_
    obtain ⟨hzS, hzt⟩ := hz
    change v (z - t₁) < η at hzt
    refine d.notMem_of_hole (memU_T ht'U) ?_ hzS
    rw [hρt']
    exact (v_sub_le_max z t₁ t').trans_lt (max_lt hzt (by rw [Valuation.map_sub_swap]; exact (memU.1 ht'U).2))

  set Zs := d.Hol x η \ HolU with hZs
  have memZ : ∀ {t}, t ∈ Zs ↔ t ∈ d.Hol x η ∧ η ≤ v (t - t₁) := fun {t} => by
    rw [hZs, Finset.mem_sdiff, memU, not_and, not_lt]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2 h1⟩, fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩⟩

  have hSA : ∀ z : K, s ≤ v (z - t₁) → v (z - t₁) ≤ η → (∀ ζ ∈ Zs, η ≤ v (z - ζ)) →
      (∀ ξ ∈ HolU, s ≤ v (z - ξ)) → z ∈ d.S := fun z _ h2 h3 h4 =>
    d.memS_of hx hη hcl ((hxt z).1 h2) fun t ht => by
      by_cases htU : t ∈ HolU
      · exact (hsU t htU).2.trans (h4 t htU)
      · exact ((hcl t (d.mem_Hol.1 ht).1).1 (d.mem_Hol.1 ht).2).trans (h3 t (Finset.mem_sdiff.2 ⟨ht, htU⟩))
  set A : Set K := {z | s ≤ v (z - t₁) ∧ v (z - t₁) ≤ η ∧ (∀ ζ ∈ Zs, η ≤ v (z - ζ)) ∧
    ∀ ξ ∈ HolU, s ≤ v (z - ξ)} with hA
  have hUA : d.P A := by
    exact d.annP t₁ πη πs hπη hπs0 hs_lt Zs (fun ζ hζ => by rw [Valuation.map_sub_swap]; exact (memZ.1 hζ).2)
      HolU (fun ξ hξ => by rw [Valuation.map_sub_swap]; exact (hsU ξ hξ).1) hSA
  have hHol : d.Hol t₁ s = HolU := by
    ext t
    rw [d.mem_Hol, memU, d.mem_Hol]
    constructor
    · rintro ⟨htT, hts⟩
      exact ⟨⟨htT, (v_sub_le_max t t₁ x).trans (max_le (hts.trans hs_le) ht₁x)⟩, hts.trans_lt hs_lt⟩
    · rintro ⟨⟨htT, htx⟩, htlt⟩
      exact ⟨htT, (hsU t (memU.2 ⟨d.mem_Hol.2 ⟨htT, htx⟩, htlt⟩)).1⟩
  have hgenA : d.gen t₁ s ⊆ A := fun z hz => by
    obtain ⟨hz1, hz2⟩ := hz
    rw [hHol] at hz2
    have hzt : v (z - t₁) = s := le_antisymm hz1 (hz2 t₁ ht₁U)
    refine ⟨hzt.ge, hz1.trans hs_le, fun ζ hζ => ?_, hz2⟩
    have hlt : v (z - t₁) < v (t₁ - ζ) := by
      rw [hzt, Valuation.map_sub_swap]; exact hs_lt.trans_le (memZ.1 hζ).2
    rw [v_sub_eq_of_lt hlt, Valuation.map_sub_swap]; exact (memZ.1 hζ).2
  have hsub : d.S ∩ {z | v (z - t₁) < η} ⊆ A ∪ (d.S ∩ {z | v (z - t₁) ≤ s}) := by
    rintro z ⟨hzS, hzt⟩
    change v (z - t₁) < η at hzt
    by_cases hzs : v (z - t₁) ≤ s
    · exact Or.inr ⟨hzS, hzs⟩
    push Not at hzs
    refine Or.inl ⟨hzs.le, hzt.le, fun ζ hζ => ?_, fun ξ hξ => ?_⟩
    · have hlt : v (z - t₁) < v (t₁ - ζ) := by
        rw [Valuation.map_sub_swap _ t₁]; exact hzt.trans_le (memZ.1 hζ).2
      rw [v_sub_eq_of_lt hlt, Valuation.map_sub_swap]; exact (memZ.1 hζ).2
    · have hlt : v (t₁ - ξ) < v (z - t₁) := by rw [Valuation.map_sub_swap]; exact (hsU ξ hξ).1.trans_lt hzs
      rw [v_sub_eq_of_lt' hlt]; exact hzs.le
  have hsmall : d.P (d.S ∩ {z | v (z - t₁) ≤ s}) := by
    by_cases hsingle : ∃ t₂ ∈ HolU, ∀ t ∈ HolU, v (t - t₂) < s
    ·
      obtain ⟨t₂, ht₂, hall⟩ := hsingle
      have hex : ∃ t' ∈ HolU, v (d.ρ t') = s := by
        rcases Finset.mem_union.1 hπs_mem with h | h
        · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
          exact absurd hall (hdiff t ht hteq.symm t₂ ht₂)
        · obtain ⟨t, ht, hteq⟩ := Finset.mem_image.1 h
          exact ⟨t, ht, by rw [hteq]⟩
      obtain ⟨t', ht', hρt'⟩ := hex
      refine d.P_mono (fun z hz => hgenA ?_) hUA
      obtain ⟨hzS, hzt⟩ := hz
      change v (z - t₁) ≤ s at hzt
      refine ⟨hzt, fun t ht => ?_⟩
      rw [hHol] at ht
      by_contra hlt
      push Not at hlt
      refine d.notMem_of_hole (memU_T ht') ?_ hzS
      rw [hρt']
      calc v (z - t') ≤ max (v (z - t₂)) (v (t₂ - t')) := v_sub_le_max z t₂ t'
        _ < s := max_lt ((v_sub_le_max z t t₂).trans_lt (max_lt hlt (hall t ht)))
            (by rw [Valuation.map_sub_swap]; exact hall t' ht')
    ·
      have hsingle' : ¬ ∃ t₂ ∈ d.Hol t₁ s, ∀ t ∈ d.Hol t₁ s, v (t - t₂) < s := by rwa [hHol]
      have hμ' : d.μ t₁ s < n := by
        have hμt : d.μ t₁ s = 2 * HolU.card := by rw [μ, if_neg hsingle', add_zero, hHol]
        rw [hμt]
        refine lt_of_lt_of_le ?_ hμ
        by_cases hall : HolU = d.Hol x η
        · have hsing : ∃ t₁' ∈ d.Hol x η, ∀ t ∈ d.Hol x η, v (t - t₁') < η :=
            ⟨t₁, ht₁, fun t ht => (memU.1 (hall.symm ▸ ht)).2⟩
          rw [μ, if_pos hsing, hall]; omega
        · have hss : HolU ⊂ d.Hol x η := by
            rw [hHolU, Finset.filter_ssubset]
            by_contra hcon
            push Not at hcon
            exact hall (Finset.filter_eq_self.2 hcon)
          have := Finset.card_lt_card hss
          rw [μ]; omega
      exact IH _ hμ' t₁ πs hπs0 le_rfl ht₁c (hs_le.trans hη)
  exact d.P_mono hsub (d.P_union hUA hsmall)

theorem down (n : ℕ) : ∀ (x πη : K), πη ≠ 0 → d.μ x (v πη) ≤ n → v (x - d.c) ≤ R → v πη ≤ R →
    d.P (d.S ∩ {z | v (z - x) ≤ v πη}) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x πη hπη hμ hx hη
    by_cases hcl : d.Clean x (v πη)
    · refine d.P_mono (d.cover x (v πη)) (d.P_union (d.P_gen hπη hx hη hcl) (d.P_biUnion _ _ fun t₁ ht₁ => ?_))
      exact d.class_step n IH x πη t₁ hπη hμ hx hη hcl ht₁
    · exact d.P_of_forall_not (d.forall_notMem_of_not_clean hcl)

theorem P_S : d.P d.S := by
  have h := d.down _ d.c d.R₀ d.hR₀ le_rfl (by rw [sub_self, map_zero]; exact zero_le') le_rfl
  refine d.P_mono (fun z hz => ?_) h
  exact ⟨hz, ((d.hS z).1 hz).1⟩

end CData

end CoverDrv

namespace MinMod

open IdAnn Polynomial CerednikDrinfeld.Omega

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem exists_min {P Q : K → Prop} (hP : ∀ δ δ' : K, v δ' ≤ v δ → P δ → P δ') (hQ : ∀ δ δ' : K, v δ' ≤ v δ → Q δ → Q δ')
    (h1 : ∃ δ : K, δ ≠ 0 ∧ P δ) (h2 : ∃ δ : K, δ ≠ 0 ∧ Q δ) : ∃ δ : K, δ ≠ 0 ∧ P δ ∧ Q δ := by
  obtain ⟨δ₁, h₁0, h₁⟩ := h1
  obtain ⟨δ₂, h₂0, h₂⟩ := h2
  rcases le_total (v δ₁) (v δ₂) with h | h
  · exact ⟨δ₁, h₁0, h₁, hQ δ₂ δ₁ h h₂⟩
  · exact ⟨δ₂, h₂0, hP δ₁ δ₂ h h₁, h₂⟩

theorem exists_min_finset {ι : Type} (s : Finset ι) (P : ι → K → Prop)
    (hP : ∀ i (δ δ' : K), v δ' ≤ v δ → P i δ → P i δ') (h : ∀ i ∈ s, ∃ δ : K, δ ≠ 0 ∧ P i δ) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ i ∈ s, P i δ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ0, hδa, hδs⟩ := exists_min (P := P a) (Q := fun δ => ∀ i ∈ s, P i δ) (hP a)
      (fun δ δ' hle h i hi => hP i δ δ' hle (h i hi))
      (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨δ, hδ0, fun i hi => by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hδa
      · exact hδs i hi⟩

variable [CompleteSpace K] [IsAlgClosed K]

theorem disc (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, v π ≤ v (c - ζ))
    (hS : ∀ z : K, v (z - c) ≤ v π → (∀ ζ ∈ Z, v π ≤ v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) (h0 : ∀ z : ↥S, Z1.InF c π Z (z : K) → f z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, Z1.InF c π Z (z : K) → v δ ≤ v (f z) := by
  classical
  have hvπ : 0 < v π := (Valuation.pos_iff _).mpr hπ

  have hcF : Z1.InF c π Z c := ⟨by rw [sub_self, map_zero]; exact zero_le', hZ⟩
  have hcS : c ∈ S := hS c hcF.1 hcF.2
  set z₁ : ↥S := ⟨c, hcS⟩ with hz₁
  have hz₁F : Z1.InF c π Z (z₁ : K) := hcF
  have hfz₁ : f z₁ ≠ 0 := h0 z₁ hz₁F
  have hm : 0 < v (f z₁) := (Valuation.pos_iff _).mpr hfz₁

  obtain ⟨r, hpf, ⟨b, hb⟩, hlim⟩ := (mem_holOn_iff (K := K) f).mp hf
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have hm0 : vRestrict K (f z₁) ≠ 0 := (Valuation.ne_zero_iff _).mpr hfz₁
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hm0))
  have happ : ∀ z : ↥S, v ((r k).evalAt z - f z) < v (f z₁) := fun z =>
    (v_lt_iff_vRestrict_lt K _ _).2 (by simpa only [Units.val_mk0] using hk k le_rfl z)
  set P : K[X] := (r k).num with hP
  set Q : K[X] := (r k).den with hQ
  have hrz : ∀ z : K, (r k).evalAt z = P.eval z / Q.eval z := fun z => rfl
  have hQz₁ : Q.eval (z₁ : K) ≠ 0 := hpf k z₁ z₁.2
  have hQ0 : Q ≠ 0 := fun h => hQz₁ (by rw [h, eval_zero])
  have hrz₁ : v ((r k).evalAt z₁) = v (f z₁) := Z1.v_eq_of_v_sub_lt (happ z₁)
  have hP0 : P ≠ 0 := by
    intro h
    have : (r k).evalAt z₁ = 0 := by rw [hrz, h, eval_zero, zero_div]
    rw [this, map_zero] at hrz₁
    exact hm.ne' hrz₁.symm
  have hQgen : ∀ z : K, Z1.InF c π Z z → ∀ β ∈ Q.roots, ¬ v (z - β) < v π := by
    intro z hz β hβ hlt
    have hβF : Z1.InF c π Z β := Z1.inF_of_v_sub_lt hz (by rw [Z1.v_sub_comm]; exact hlt)
    exact hpf k β (hS β hβF.1 hβF.2) ((mem_roots hQ0).1 hβ)
  obtain ⟨y, hyc, hygen⟩ := Z1.exists_generic_disc c π hπ (Z.val + P.roots + Q.roots)
  have hyF : Z1.InF c π Z y :=
    ⟨hyc, fun ζ hζ => hygen ζ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hζ))))⟩
  have hyP : ∀ α ∈ P.roots, ¬ v (y - α) < v π := fun α hα =>
    not_lt.mpr (hygen α (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hα)))))
  have hyQ : ∀ β ∈ Q.roots, ¬ v (y - β) < v π := fun β hβ => not_lt.mpr (hygen β (Multiset.mem_add.mpr (Or.inr hβ)))
  have hQconst : ∀ z : K, Z1.InF c π Z z → v (Q.eval z) = v (Q.eval y) := fun z hz =>
    Z1.v_eval_eq_of_generic Q hyc hyQ hz.1 (hQgen z hz)
  have hry : v (f z₁) ≤ v ((r k).evalAt y) := by
    rw [← hrz₁, hrz, hrz, map_div₀, map_div₀, hQconst z₁ hz₁F]
    exact div_le_div_of_nonneg_right (Z1.v_eval_le_of_generic P hyc hyP hz₁F.1) zero_le'

  have hoff : ∀ z : ↥S, Z1.InF c π Z (z : K) → (∀ α ∈ P.roots, ¬ v ((z : K) - α) < v π) → v (f z₁) ≤ v (f z) := by
    intro z hzF hzP
    have hPz : v (P.eval (z : K)) = v (P.eval y) := Z1.v_eval_eq_of_generic P hyc hyP hzF.1 hzP
    have hrzy : v ((r k).evalAt z) = v ((r k).evalAt y) := by
      rw [hrz, hrz, map_div₀, map_div₀, hPz, hQconst z hzF]
    have hlt : v ((r k).evalAt z - f z) < v ((r k).evalAt z) := (happ z).trans_le (hrzy ▸ hry)
    have hfz : v (f z) = v ((r k).evalAt z) := by
      rw [Z1.v_sub_comm] at hlt; exact Z1.v_eq_of_v_sub_lt hlt
    rw [hfz, hrzy]; exact hry

  have hcls : ∀ α ∈ P.roots.toFinset, ∃ δ : K, δ ≠ 0 ∧
      ∀ z : ↥S, Z1.InF c π Z (z : K) → v ((z : K) - α) < v π → v δ ≤ v (f z) := by
    intro α _
    by_cases hmeet : ∃ w : K, Z1.InF c π Z w ∧ v (w - α) < v π
    · obtain ⟨w, hwF, hwα⟩ := hmeet
      have hαF : Z1.InF c π Z α := Z1.inF_of_v_sub_lt hwF (by rw [Z1.v_sub_comm]; exact hwα)
      set Z' : Finset K := Z.filter fun ζ => v (c - ζ) ≤ v π with hZ'
      have hZ'eq : ∀ ζ ∈ Z', v (α - ζ) = v π := by
        intro ζ hζ
        obtain ⟨hζZ, hζc⟩ := Finset.mem_filter.mp hζ
        refine le_antisymm ?_ ?_
        · have e : α - ζ = (α - c) + (c - ζ) := by ring
          rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hαF.1 hζc)
        · have h1 := hwF.2 ζ hζZ
          have e : α - ζ = (w - ζ) - (w - α) := by ring
          rw [e, Z1.v_sub_eq_of_lt (hwα.trans_le h1)]
          exact h1
      have hS' : ∀ z : K, v (z - α) ≤ v π → (∀ ζ ∈ Z', v π ≤ v (z - ζ)) → z ∈ S := by
        intro z hzα hzZ'
        have hzc : v (z - c) ≤ v π := by
          have e : z - c = (z - α) + (α - c) := by ring
          rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hzα hαF.1)
        refine hS z hzc fun ζ hζ => ?_
        by_cases hζc : v (c - ζ) ≤ v π
        · exact hzZ' ζ (Finset.mem_filter.mpr ⟨hζ, hζc⟩)
        · rw [not_le] at hζc
          have e : z - ζ = (c - ζ) - (c - z) := by ring
          rw [e, Z1.v_sub_eq_of_lt (by rw [Z1.v_sub_comm c z]; exact hzc.trans_lt hζc)]
          exact hζc.le
      have h0' : ∀ z : ↥S, v ((z : K) - α) < v π → f z ≠ 0 := fun z hz =>
        h0 z (Z1.inF_of_v_sub_lt hαF hz)
      obtain ⟨δ, hδ0, hδ⟩ := CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero K hrk S α π hπ
        Z' hZ'eq hS' hf h0'
      exact ⟨δ, hδ0, fun z _ hz => hδ z hz⟩
    · exact ⟨1, one_ne_zero, fun z hzF hzα => absurd ⟨(z : K), hzF, hzα⟩ hmeet⟩
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := exists_min_finset P.roots.toFinset
    (fun α δ => ∀ z : ↥S, Z1.InF c π Z (z : K) → v ((z : K) - α) < v π → v δ ≤ v (f z))
    (fun α δ δ' hle h z hz hzα => hle.trans (h z hz hzα)) hcls

  obtain ⟨δ, hδ0, hδa, hδb⟩ := exists_min (P := fun δ => v δ ≤ v (f z₁))
    (Q := fun δ => ∀ z : ↥S, Z1.InF c π Z (z : K) → (∃ α ∈ P.roots, v ((z : K) - α) < v π) → v δ ≤ v (f z))
    (fun δ δ' hle h => hle.trans h) (fun δ δ' hle h z hz hex => hle.trans (h z hz hex))
    ⟨f z₁, hfz₁, le_rfl⟩ ⟨δ₁, hδ₁0, fun z hz ⟨α, hα, hzα⟩ => hδ₁ α (Multiset.mem_toFinset.mpr hα) z hz hzα⟩
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  by_cases hex : ∃ α ∈ P.roots, v ((z : K) - α) < v π
  · exact hδb z hz hex
  · push Not at hex
    exact hδa.trans (hoff z hz fun α hα => not_lt.mpr (hex α hα))

theorem ann (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (c πd πs : K) (hπd : πd ≠ 0) (hπs : πs ≠ 0) (hlt : v πs < v πd)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, v πd ≤ v (c - ζ))
    (Ξ : Finset K) (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs)
    (hS : ∀ z : K, v πs ≤ v (z - c) → v (z - c) ≤ v πd →
      (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) → (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) (h0 : ∀ z : ↥S, Z2.InA c πd πs Z Ξ (z : K) → f z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, Z2.InA c πd πs Z Ξ (z : K) → v δ ≤ v (f z) := by
  classical
  have hvs : 0 < Valued.v πs := (Valuation.pos_iff _).mpr hπs
  have hvd : 0 < Valued.v πd := (Valuation.pos_iff _).mpr hπd
  obtain ⟨r, hpf, ⟨b, hb⟩, hlim⟩ := (mem_holOn_iff (K := K) f).mp hf
  obtain ⟨B, hB0, hbB, -, h1B⟩ := exists_bound b b
  have hvB : 0 < Valued.v B := (Valuation.pos_iff _).mpr hB0
  rw [tendstoUniformly_iff_vRestrict] at hlim
  have happ : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : ↥S, Valued.v ((r k).evalAt z - f z) < Valued.v e := by
    intro e he
    have hm0 : vRestrict K e ≠ 0 := (Valuation.ne_zero_iff _).mpr he
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hm0))
    exact ⟨N, fun k hk z => (v_lt_iff_vRestrict_lt K _ _).2 (by simpa only [Units.val_mk0] using hN k hk z)⟩
  have hAS : ∀ z : K, Z2.InA c πd πs Z Ξ z → z ∈ S := fun z hz => hS z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have hrz : ∀ (k : ℕ) (z : K), (r k).evalAt z = (r k).num.eval z / (r k).den.eval z := fun k z => rfl

  obtain ⟨πm, hπm⟩ := IsAlgClosed.exists_eq_mul_self (πs * πd)
  have hvm2 : Valued.v πm * Valued.v πm = Valued.v πs * Valued.v πd := by rw [← map_mul, ← hπm, map_mul]
  have hπm0 : πm ≠ 0 := by
    intro h; rw [h, mul_zero] at hπm; exact mul_ne_zero hπs hπd hπm
  have hvm : 0 < Valued.v πm := (Valuation.pos_iff _).mpr hπm0
  have hsm : Valued.v πs ≤ Valued.v πm := by
    by_contra h; rw [not_le] at h
    have := mul_lt_mul'' h (h.trans hlt) zero_le' zero_le'
    rw [hvm2] at this; exact lt_irrefl _ this
  have hmd : Valued.v πm ≤ Valued.v πd := by
    by_contra h; rw [not_le] at h
    have := mul_lt_mul'' (hlt.trans h) h zero_le' zero_le'
    rw [hvm2] at this; exact lt_irrefl _ this

  obtain ⟨y₀, hy₀c, hy₀gen⟩ := Z2.exists_generic_circle c πm hπm0 (Z.val + Ξ.val)
  have hy₀A : Z2.InA c πd πs Z Ξ y₀ := Z2.inA_of_generic hZ hΞ hy₀c hsm hmd hy₀gen
  have hy₀S : y₀ ∈ S := hAS y₀ hy₀A
  set e₀ : K := f ⟨y₀, hy₀S⟩ with he₀
  have he₀ : e₀ ≠ 0 := h0 ⟨y₀, hy₀S⟩ hy₀A
  have hve₀ : 0 < Valued.v e₀ := (Valuation.pos_iff _).mpr he₀
  obtain ⟨Nc, hNc⟩ := happ e₀ he₀
  have hstab : ∀ j ≥ Nc, Valued.v e₀ ≤ Valued.v ((r j).evalAt y₀) := by
    intro j hj
    rw [Z1.v_eq_of_v_sub_lt (hNc j hj ⟨y₀, hy₀S⟩)]

  set e : K := e₀ * e₀ / B with he_def
  have he : e ≠ 0 := div_ne_zero (mul_ne_zero he₀ he₀) hB0
  have hve : Valued.v e = Valued.v e₀ * Valued.v e₀ / Valued.v B := by rw [he_def, map_div₀, map_mul]
  obtain ⟨N₁, hN₁⟩ := happ e he
  set k : ℕ := max Nc N₁ with hk
  set P : K[X] := (r k).num with hP
  set Q : K[X] := (r k).den with hQ
  have hQpf : ∀ z ∈ S, Q.eval z ≠ 0 := fun z hz => hpf k z hz
  have hQy₀ : Q.eval y₀ ≠ 0 := hQpf y₀ hy₀S
  have hQ0 : Q ≠ 0 := fun h => hQy₀ (by rw [h, eval_zero])
  have hrk₀ : Valued.v e₀ ≤ Valued.v ((r k).evalAt y₀) := hstab k (le_max_left _ _)
  have hP0 : P ≠ 0 := by
    intro h
    have : (r k).evalAt y₀ = 0 := by rw [hrz, ← hP, h, eval_zero, zero_div]
    rw [this, map_zero] at hrk₀
    exact absurd hrk₀ (not_le.mpr hve₀)
  have hQroots : ∀ β ∈ Q.roots, Valued.v (β - c) ≤ Valued.v πs ∨ Valued.v πd ≤ Valued.v (β - c) :=
    fun β hβ => Z2.root_not_interior hZ hΞ hS hQpf hQ0 hβ

  obtain ⟨ym, hymc, hymgen⟩ := Z2.exists_generic_circle c πm hπm0 (P.roots + (Z.val + Ξ.val))
  have hymA : Z2.InA c πd πs Z Ξ ym :=
    Z2.inA_of_generic hZ hΞ hymc hsm hmd fun b hb => hymgen b (Multiset.mem_add.mpr (Or.inr hb))
  have hymS : ym ∈ S := hAS ym hymA
  have hymP : ∀ α ∈ P.roots, ¬ Valued.v (ym - α) < Valued.v (ym - c) := fun α hα => by
    rw [hymc, not_lt]; exact hymgen α (Multiset.mem_add.mpr (Or.inl hα))
  have hymQ : ∀ β ∈ Q.roots, ¬ Valued.v (ym - β) < Valued.v (ym - c) := Z2.den_generic hΞ hS hQpf hQ0 hymA
  have hrym : Valued.v e₀ ≤ Valued.v ((r k).evalAt ym) := by
    refine hrk₀.trans ?_
    rw [hrz, hrz, map_div₀, map_div₀, ← hP, ← hQ]
    have hPle : Valued.v (P.eval y₀) ≤ Valued.v (P.eval ym) :=
      Z1.v_eval_le_of_generic P (c := c) (ρ := Valued.v πm) hymc.le
        (fun α hα => by rw [← hymc]; exact hymP α hα) hy₀c.le
    have hQeq : Valued.v (Q.eval y₀) = Valued.v (Q.eval ym) :=
      Z1.v_eval_eq_of_generic Q (c := c) (ρ := Valued.v πm) hymc.le
        (fun β hβ => by rw [← hymc]; exact hymQ β hβ) hy₀c.le
        (fun β hβ => by rw [← hy₀c]; exact Z2.den_generic hΞ hS hQpf hQ0 hy₀A β hβ)
    rw [hQeq]
    exact div_le_div_of_nonneg_right hPle zero_le'

  have hlow : ∀ z : K, Z2.InA c πd πs Z Ξ z → (∀ α ∈ P.roots, ¬ Valued.v (z - α) < Valued.v (z - c)) →
      Valued.v e ≤ Valued.v ((r k).evalAt z) := by
    intro z hzA hzP
    have hρ0 : 0 < Valued.v (z - c) := hvs.trans_le hzA.1
    have hzc0 : z - c ≠ 0 := (Valuation.pos_iff _).mp hρ0

    set π' : K := πs * πd / (z - c) with hπ'
    have hπ'0 : π' ≠ 0 := div_ne_zero (mul_ne_zero hπs hπd) hzc0
    have hvπ' : Valued.v π' = Valued.v πs * Valued.v πd / Valued.v (z - c) := by rw [hπ', map_div₀, map_mul]
    have hρρ' : Valued.v πm * Valued.v πm = Valued.v (z - c) * Valued.v π' := by
      rw [hvm2, hvπ', ← mul_div_assoc, mul_div_cancel_left₀ _ hρ0.ne']
    have hsπ' : Valued.v πs ≤ Valued.v π' := by
      rw [hvπ', le_div_iff₀ hρ0]; exact mul_le_mul' le_rfl hzA.2.1
    have hπ'd : Valued.v π' ≤ Valued.v πd := by
      rw [hvπ', div_le_iff₀ hρ0, mul_comm]; exact mul_le_mul' le_rfl hzA.1

    obtain ⟨y', hy'c, hy'gen⟩ := Z2.exists_generic_circle c π' hπ'0 (P.roots + (Z.val + Ξ.val))
    have hy'A : Z2.InA c πd πs Z Ξ y' :=
      Z2.inA_of_generic hZ hΞ hy'c hsπ' hπ'd fun b hb => hy'gen b (Multiset.mem_add.mpr (Or.inr hb))
    have hy'S : y' ∈ S := hAS y' hy'A
    have hy'P : ∀ α ∈ P.roots, ¬ Valued.v (y' - α) < Valued.v (y' - c) := fun α hα => by
      rw [hy'c, not_lt]; exact hy'gen α (Multiset.mem_add.mpr (Or.inl hα))
    have hy'Q := Z2.den_generic hΞ hS hQpf hQ0 hy'A
    have hzQ := Z2.den_generic hΞ hS hQpf hQ0 hzA

    have hPz := Z2.v_eval_eq_prod_max P hzP
    have hPy' := Z2.v_eval_eq_prod_max P hy'P
    have hPm := Z2.v_eval_eq_prod_max P hymP
    have hQz := Z2.v_eval_eq_prod_max Q hzQ
    have hQy' := Z2.v_eval_eq_prod_max Q hy'Q
    have hQm := Z2.v_eval_eq_prod_max Q hymQ
    rw [hy'c] at hPy' hQy'
    rw [hymc] at hPm hQm
    have hPconv : Valued.v (P.eval ym) * Valued.v (P.eval ym) ≤ Valued.v (P.eval z) * Valued.v (P.eval y') := by
      have hh := Z2.prod_max_mul_le P.roots c hρρ'
      rw [hPm, hPz, hPy']
      calc Valued.v P.leadingCoeff * (P.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod *
            (Valued.v P.leadingCoeff * (P.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod)
          = (Valued.v P.leadingCoeff * Valued.v P.leadingCoeff) *
            ((P.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod *
             (P.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod) := by ac_rfl
        _ ≤ (Valued.v P.leadingCoeff * Valued.v P.leadingCoeff) *
            ((P.roots.map fun α => max (Valued.v (z - c)) (Valued.v (α - c))).prod *
             (P.roots.map fun α => max (Valued.v π') (Valued.v (α - c))).prod) := mul_le_mul' le_rfl hh
        _ = _ := by ac_rfl
    have hQlin : Valued.v (Q.eval ym) * Valued.v (Q.eval ym) = Valued.v (Q.eval z) * Valued.v (Q.eval y') := by
      have hh := Z2.prod_max_mul_eq Q.roots c hρρ' hzA.1 hzA.2.1 hsπ' hπ'd hsm hmd hQroots
      rw [hQm, hQz, hQy']
      calc Valued.v Q.leadingCoeff * (Q.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod *
            (Valued.v Q.leadingCoeff * (Q.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod)
          = (Valued.v Q.leadingCoeff * Valued.v Q.leadingCoeff) *
            ((Q.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod *
             (Q.roots.map fun α => max (Valued.v πm) (Valued.v (α - c))).prod) := by ac_rfl
        _ = (Valued.v Q.leadingCoeff * Valued.v Q.leadingCoeff) *
            ((Q.roots.map fun α => max (Valued.v (z - c)) (Valued.v (α - c))).prod *
             (Q.roots.map fun α => max (Valued.v π') (Valued.v (α - c))).prod) := by rw [hh]
        _ = _ := by ac_rfl

    have hvQm : 0 < Valued.v (Q.eval ym) := (Valuation.pos_iff _).mpr (hQpf ym hymS)
    have key : Valued.v ((r k).evalAt ym) * Valued.v ((r k).evalAt ym) ≤
        Valued.v ((r k).evalAt z) * Valued.v ((r k).evalAt y') := by
      rw [hrz, hrz, hrz, ← hP, ← hQ, map_div₀, map_div₀, map_div₀, div_mul_div_comm, div_mul_div_comm, ← hQlin]
      exact div_le_div_of_nonneg_right hPconv zero_le'
    have hry' : Valued.v ((r k).evalAt y') ≤ Valued.v B := (hb k ⟨y', hy'S⟩).trans hbB
    have : Valued.v e₀ * Valued.v e₀ ≤ Valued.v ((r k).evalAt z) * Valued.v B :=
      (mul_le_mul' hrym hrym).trans (key.trans (mul_le_mul' le_rfl hry'))
    rw [hve, div_le_iff₀ hvB]
    exact this

  have hoff : ∀ z : ↥S, Z2.InA c πd πs Z Ξ (z : K) → (∀ α ∈ P.roots, ¬ Valued.v ((z : K) - α) < Valued.v ((z : K) - c)) →
      Valued.v e ≤ Valued.v (f z) := by
    intro z hzA hzP
    have h1 := hlow z hzA hzP
    have h2 := hN₁ k (le_max_right _ _) z
    have hlt' : Valued.v ((r k).evalAt z - f z) < Valued.v ((r k).evalAt z) := h2.trans_le h1
    have hfz : Valued.v (f z) = Valued.v ((r k).evalAt z) := by
      rw [Z1.v_sub_comm] at hlt'; exact Z1.v_eq_of_v_sub_lt hlt'
    rw [hfz]; exact h1

  have hcls : ∀ α ∈ P.roots.toFinset, ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, Z2.InA c πd πs Z Ξ (z : K) →
      Valued.v ((z : K) - α) < Valued.v ((z : K) - c) → Valued.v δ ≤ Valued.v (f z) := by
    intro α _
    by_cases hmeet : ∃ w : K, Z2.InA c πd πs Z Ξ w ∧ Valued.v (w - α) < Valued.v (w - c)
    · obtain ⟨w, hwA, hwα⟩ := hmeet
      have hαc : Valued.v (α - c) = Valued.v (w - c) := by
        have e1 : α - c = (w - c) - (w - α) := by ring
        rw [e1, Z1.v_sub_eq_of_lt hwα]
      have hπα0 : α - c ≠ 0 := (Valuation.pos_iff _).mp (by rw [hαc]; exact hvs.trans_le hwA.1)
      have hsα : Valued.v πs ≤ Valued.v (α - c) := by rw [hαc]; exact hwA.1
      have hαd : Valued.v (α - c) ≤ Valued.v πd := by rw [hαc]; exact hwA.2.1

      set Z' : Finset K := insert c ((Z.filter fun ζ => Valued.v (α - ζ) = Valued.v (α - c)) ∪
        (Ξ.filter fun ξ => Valued.v (α - ξ) = Valued.v (α - c))) with hZ'
      have hZ'eq : ∀ ζ ∈ Z', Valued.v (α - ζ) = Valued.v (α - c) := by
        intro ζ hζ
        rcases Finset.mem_insert.mp hζ with rfl | hζ
        · rfl
        rcases Finset.mem_union.mp hζ with hζ | hζ
        · exact (Finset.mem_filter.mp hζ).2
        · exact (Finset.mem_filter.mp hζ).2
      have hS' : ∀ z : K, Valued.v (z - α) ≤ Valued.v (α - c) →
          (∀ ζ ∈ Z', Valued.v (α - c) ≤ Valued.v (z - ζ)) → z ∈ S := by
        intro z hzα hzZ'
        have hzc : Valued.v (z - c) = Valued.v (α - c) := by
          refine le_antisymm ?_ (hzZ' c (Finset.mem_insert_self _ _))
          have e1 : z - c = (z - α) + (α - c) := by ring
          rw [e1]; exact (Valuation.map_add _ _ _).trans (max_le hzα le_rfl)
        refine hAS z ⟨by rw [hzc]; exact hsα, by rw [hzc]; exact hαd, fun ζ hζ => ?_, fun ξ hξ => ?_⟩
        · rcases eq_or_lt_of_le hαd with htop | htop
          ·
            by_cases hζ' : Valued.v (α - ζ) = Valued.v (α - c)
            · rw [← htop]; exact hzZ' ζ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hζ, hζ'⟩)))
            · rcases eq_or_lt_of_le ((hZ ζ hζ).trans_eq' htop.symm) with hcζ | hcζ
              ·
                exfalso
                have hlt' : Valued.v (α - ζ) < Valued.v (α - c) := by
                  refine lt_of_le_of_ne ?_ hζ'
                  have e1 : α - ζ = (α - c) + (c - ζ) := by ring
                  rw [e1]; exact (Valuation.map_add _ _ _).trans (max_le le_rfl hcζ.ge)
                have : Valued.v (w - ζ) < Valued.v πd := by
                  have e1 : w - ζ = (w - α) + (α - ζ) := by ring
                  rw [e1, ← htop]
                  exact (Valuation.map_add _ _ _).trans_lt (max_lt (hwα.trans_eq hαc.symm) hlt')
                exact absurd (hwA.2.2.1 ζ hζ) (not_le.mpr this)
              · have e1 : z - ζ = (c - ζ) - (c - z) := by ring
                rw [e1, Z1.v_sub_eq_of_lt (by rw [Z1.v_sub_comm c z, hzc]; exact hcζ)]
                exact hZ ζ hζ
          · exact Z2.zcond_of_lt hZ (by rw [hzc]; exact htop) ζ hζ
        · rcases eq_or_lt_of_le hsα with hbot | hbot
          · by_cases hξ' : Valued.v (α - ξ) = Valued.v (α - c)
            · rw [hbot]; exact hzZ' ξ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hξ, hξ'⟩)))
            · exfalso
              have hlt' : Valued.v (α - ξ) < Valued.v (α - c) := by
                refine lt_of_le_of_ne ?_ hξ'
                have e1 : α - ξ = (α - c) + (c - ξ) := by ring
                rw [e1]; exact (Valuation.map_add _ _ _).trans (max_le le_rfl ((hΞ ξ hξ).trans_eq hbot))
              have : Valued.v (w - ξ) < Valued.v πs := by
                have e1 : w - ξ = (w - α) + (α - ξ) := by ring
                rw [e1, hbot]
                exact (Valuation.map_add _ _ _).trans_lt (max_lt (hwα.trans_eq hαc.symm) hlt')
              exact absurd (hwA.2.2.2 ξ hξ) (not_le.mpr this)
          · exact Z2.xcond_of_lt hΞ (by rw [hzc]; exact hbot) ξ hξ
      have hαA : Z2.InA c πd πs Z Ξ α := Z2.inA_of_v_sub_lt hΞ hwA hwα
      have h0' : ∀ z : ↥S, Valued.v ((z : K) - α) < Valued.v (α - c) → f z ≠ 0 := fun z hz =>
        h0 z (Z2.inA_of_v_sub_lt hΞ hαA (by rw [Z1.v_sub_comm]; exact hz))
      obtain ⟨δ, hδ0, hδ⟩ := CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero K hrk S α (α - c)
        hπα0 Z' hZ'eq hS' hf h0'
      refine ⟨δ, hδ0, fun z _ hz => hδ z ?_⟩
      have hzc : Valued.v ((z : K) - c) = Valued.v (α - c) := by
        have e1 : α - c = ((z : K) - c) - ((z : K) - α) := by ring
        rw [e1, Z1.v_sub_eq_of_lt hz]
      rw [← hzc]; exact hz
    · exact ⟨1, one_ne_zero, fun z hzA hzα => absurd ⟨(z : K), hzA, hzα⟩ hmeet⟩
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := exists_min_finset P.roots.toFinset
    (fun α δ => ∀ z : ↥S, Z2.InA c πd πs Z Ξ (z : K) → Valued.v ((z : K) - α) < Valued.v ((z : K) - c) →
      Valued.v δ ≤ Valued.v (f z))
    (fun α δ δ' hle h z hz hzα => hle.trans (h z hz hzα)) hcls
  obtain ⟨δ, hδ0, hδa, hδb⟩ := exists_min (P := fun δ => Valued.v δ ≤ Valued.v e)
    (Q := fun δ => ∀ z : ↥S, Z2.InA c πd πs Z Ξ (z : K) →
      (∃ α ∈ P.roots, Valued.v ((z : K) - α) < Valued.v ((z : K) - c)) → Valued.v δ ≤ Valued.v (f z))
    (fun δ δ' hle h => hle.trans h) (fun δ δ' hle h z hz hex => hle.trans (h z hz hex))
    ⟨e, he, le_rfl⟩ ⟨δ₁, hδ₁0, fun z hz ⟨α, hα, hzα⟩ => hδ₁ α (Multiset.mem_toFinset.mpr hα) z hz hzα⟩
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  by_cases hex : ∃ α ∈ P.roots, Valued.v ((z : K) - α) < Valued.v ((z : K) - c)
  · exact hδb z hz hex
  · push Not at hex
    exact hδa.trans (hoff z hz fun α hα => not_lt.mpr (hex α hα))

end MinMod

open IdAnn Polynomial CerednikDrinfeld.Omega in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : ↥(affinoid ϖ n) → K} (hG : G ∈ holOn K (affinoid ϖ n)) (hG0 : ∀ z : ↥(affinoid ϖ n), G z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥(affinoid ϖ n), Valued.v δ ≤ Valued.v (G z) := by
  classical
  set p : K := algebraMap K₀ K ϖ.ϖ with hp
  have hvp : 0 < Valued.v p := ϖ.pos
  have hp0 : p ≠ 0 := (Valuation.pos_iff _).1 hvp
  have hp1 : Valued.v p < 1 := ϖ.lt_one
  have hP1 : 1 ≤ (Valued.v p)⁻¹ := (one_le_inv₀ hvp).2 hp1.le

  by_cases hemp : IsEmpty ↥(affinoid ϖ n)
  · exact ⟨1, one_ne_zero, fun z => (hemp.false z).elim⟩
  rw [not_isEmpty_iff] at hemp
  obtain ⟨⟨c₀, hc₀⟩⟩ := hemp

  obtain ⟨T₀, hT₀⟩ := hfin
  set T : Finset K := (T₀.image (algebraMap K₀ K)).filter fun t => Valued.v t ≤ (Valued.v p)⁻¹ ^ n with hT
  have hS : ∀ z : K, z ∈ affinoid ϖ n ↔
      Valued.v (z - 0) ≤ Valued.v (p⁻¹ ^ n) ∧ ∀ t ∈ T, Valued.v (p ^ n) ≤ Valued.v (z - t) := fun z => by
    rw [sub_zero, map_pow, map_inv₀, map_pow]
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨hz1, fun t ht => ?_⟩
      obtain ⟨ht, hvt⟩ := Finset.mem_filter.1 ht
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ht
      exact hz2 a hvt
    · rintro ⟨hz1, hz2⟩
      refine ⟨hz1, fun a ha => ?_⟩
      obtain ⟨t, htT, hlt⟩ := hT₀ a ha
      have hvt : Valued.v (algebraMap K₀ K t) ≤ (Valued.v p)⁻¹ ^ n := by
        have : algebraMap K₀ K t = algebraMap K₀ K a - (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
        rw [this]
        refine (Valuation.map_sub _ _ _).trans (max_le ha (hlt.le.trans ?_))
        exact (pow_le_one₀ zero_le' hp1.le).trans (one_le_pow₀ hP1)
      have hmem : algebraMap K₀ K t ∈ T := Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ htT, hvt⟩
      have h1 := hz2 _ hmem
      have : z - algebraMap K₀ K a = (z - algebraMap K₀ K t) - (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (hlt.trans_le h1)]
      exact h1

  have hR0 : (p⁻¹ ^ n : K) ≠ 0 := pow_ne_zero _ (inv_ne_zero hp0)
  have hc₀0 : Valued.v (c₀ - 0) ≤ Valued.v (p⁻¹ ^ n : K) := ((hS c₀).1 hc₀).1
  have hS' : ∀ z : K, z ∈ affinoid ϖ n ↔
      Valued.v (z - c₀) ≤ Valued.v (p⁻¹ ^ n : K) ∧ ∀ t ∈ T, Valued.v (p ^ n) ≤ Valued.v (z - t) := fun z => by
    rw [hS]
    refine and_congr_left fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · exact (CoverDrv.v_sub_le_max z 0 c₀).trans (max_le h (by rw [Valuation.map_sub_swap]; exact hc₀0))
    · exact (CoverDrv.v_sub_le_max z c₀ 0).trans (max_le h hc₀0)

  let d : CoverDrv.CData K :=
    { S := affinoid ϖ n, T := T, ρ := fun _ => p ^ n, c := c₀, R₀ := p⁻¹ ^ n, hR₀ := hR0,
      hρ := fun _ _ => pow_ne_zero _ hp0, hS := hS', hc := hc₀,
      P := fun A => ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥(affinoid ϖ n), (z : K) ∈ A → Valued.v δ ≤ Valued.v (G z),
      P_mono := fun hAB ⟨δ, hδ0, hδ⟩ => ⟨δ, hδ0, fun z hz => hδ z (hAB hz)⟩,
      P_union := fun ⟨δ₁, h₁0, h₁⟩ ⟨δ₂, h₂0, h₂⟩ => by
        rcases le_total (Valued.v δ₁) (Valued.v δ₂) with h | h
        · exact ⟨δ₁, h₁0, fun z hz => hz.elim (h₁ z) (fun hz => h.trans (h₂ z hz))⟩
        · exact ⟨δ₂, h₂0, fun z hz => hz.elim (fun hz => h.trans (h₁ z hz)) (h₂ z)⟩,
      P_empty := ⟨1, one_ne_zero, fun z hz => absurd hz (Set.notMem_empty _)⟩,
      discP := fun x π hπ Z hZ hsub => by
        obtain ⟨δ, hδ0, hδ⟩ := MinMod.disc hrk (affinoid ϖ n) x π hπ Z hZ hsub hG (fun z _ => hG0 z)
        exact ⟨δ, hδ0, fun z hz => hδ z hz⟩,
      annP := fun x πd πs hπd hπs hlt Z hZ Ξ hΞ hsub => by
        obtain ⟨δ, hδ0, hδ⟩ := MinMod.ann hrk (affinoid ϖ n) x πd πs hπd hπs hlt Z hZ Ξ hΞ hsub hG (fun z _ => hG0 z)
        exact ⟨δ, hδ0, fun z hz => hδ z hz⟩ }
  obtain ⟨δ, hδ0, hδ⟩ := d.P_S
  exact ⟨δ, hδ0, fun z => hδ z z.2⟩

end
end S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero (solution)
