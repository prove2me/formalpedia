-- Prove2me | solution 1 for CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/95f50542-a485-57ad-861d-c91064556cd9

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover.CerednikDrinfeld.Omega"

noncomputable section
open Classical

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair RatPair.const holOn mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt"
namespace SHC
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

open Polynomial

namespace B9

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "𝓋" => (Valued.v (R := K))

theorem v_sub_comm (a b : K) : 𝓋 (a - b) = 𝓋 (b - a) := Valuation.map_sub_swap _ a b

theorem v_sub_le_max (a b c : K) : 𝓋 (a - c) ≤ max (𝓋 (a - b)) (𝓋 (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add _ _ _

theorem v_sub_eq_of_lt {a b c : K} (h : 𝓋 (a - b) < 𝓋 (b - c)) : 𝓋 (a - c) = 𝓋 (b - c) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add_eq_of_lt_right _ h

section Generic
variable [IsAlgClosed K]

theorem exists_unit_generic (W : Finset K) : ∃ u : K, 𝓋 u = 1 ∧ ∀ w ∈ W, 1 ≤ 𝓋 (u - w) := by
  classical
  let W₁ := W.filter fun w => 𝓋 w = 1
  let p : K[X] := X * ∏ w ∈ W₁, (X - C w)
  have hmonic : p.Monic := monic_X.mul (monic_prod_of_monic _ _ fun w _ => monic_X_sub_C w)
  have hdegp : 0 < p.degree := by
    have : p.natDegree = 1 + W₁.card := by
      rw [show p = X * ∏ w ∈ W₁, (X - C w) from rfl, natDegree_mul X_ne_zero (monic_prod_of_monic _ _ fun w _ => monic_X_sub_C w).ne_zero,
        natDegree_X, natDegree_prod_of_monic _ _ fun w _ => monic_X_sub_C w]
      simp
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [this]; omega)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (p - C 1) (by rw [degree_sub_C hdegp]; exact hdegp.ne')
  have hu' : u * ∏ w ∈ W₁, (u - w) = 1 := by
    have := hu
    rw [IsRoot, eval_sub, eval_C, sub_eq_zero, eval_mul, eval_X, eval_prod] at this
    simpa using this
  have hv : 𝓋 u * ∏ w ∈ W₁, 𝓋 (u - w) = 1 := by
    rw [← map_prod, ← Valuation.map_mul, hu', Valuation.map_one]

  have hvu : 𝓋 u = 1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    ·
      have : ∏ w ∈ W₁, 𝓋 (u - w) = 1 := by
        refine Finset.prod_eq_one fun w hw => ?_
        have hw1 : 𝓋 w = 1 := (Finset.mem_filter.mp hw).2
        rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hw1]; exact hlt), hw1]
      rw [this, mul_one] at hv
      exact hne hv
    · have : ∀ w ∈ W₁, 𝓋 (u - w) = 𝓋 u := fun w hw => by
        have hw1 : 𝓋 w = 1 := (Finset.mem_filter.mp hw).2
        exact Valuation.map_sub_eq_of_lt_left _ (by rw [hw1]; exact hgt)
      rw [Finset.prod_congr rfl this, Finset.prod_const] at hv
      have h1 : (1 : Γ₀) < 𝓋 u * 𝓋 u ^ W₁.card :=
        lt_of_lt_of_le hgt (le_mul_of_one_le_right' (one_le_pow_of_one_le' hgt.le _))
      exact absurd hv h1.ne'
  refine ⟨u, hvu, fun w hw => ?_⟩
  rcases lt_trichotomy (𝓋 w) 1 with hlt | heq | hgt
  · rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hvu]; exact hlt), hvu]
  ·
    have hwW : w ∈ W₁ := Finset.mem_filter.mpr ⟨hw, heq⟩
    have hle : ∀ x ∈ W₁, 𝓋 (u - x) ≤ 1 := fun x hx => by
      have hx1 : 𝓋 x = 1 := (Finset.mem_filter.mp hx).2
      calc 𝓋 (u - x) ≤ max (𝓋 u) (𝓋 x) := Valuation.map_sub _ _ _
        _ = 1 := by rw [hvu, hx1, max_self]
    rw [hvu, one_mul] at hv
    by_contra hlt
    push_neg at hlt
    have : ∏ x ∈ W₁, 𝓋 (u - x) < 1 := by
      rw [← Finset.mul_prod_erase _ _ hwW]
      calc 𝓋 (u - w) * ∏ x ∈ W₁.erase w, 𝓋 (u - x) ≤ 𝓋 (u - w) * 1 :=
            mul_le_mul_right (Finset.prod_le_one' fun x hx => hle x (Finset.mem_of_mem_erase hx)) _
        _ < 1 := by rw [mul_one]; exact hlt
    exact absurd hv this.ne
  · rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hvu]; exact hgt)]; exact hgt.le

theorem exists_generic (a s : K) (hs : s ≠ 0) (Z : Finset K) :
    ∃ z : K, 𝓋 (z - a) = 𝓋 s ∧ ∀ ζ ∈ Z, 𝓋 s ≤ 𝓋 (z - ζ) := by
  obtain ⟨u, hu, hgen⟩ := exists_unit_generic (K := K) (Z.image fun ζ => (ζ - a) / s)
  refine ⟨a + s * u, by rw [add_sub_cancel_left, Valuation.map_mul, hu, mul_one], fun ζ hζ => ?_⟩
  have h := hgen ((ζ - a) / s) (Finset.mem_image_of_mem _ hζ)
  have e : a + s * u - ζ = s * (u - (ζ - a) / s) := by field_simp; ring
  rw [e, Valuation.map_mul]
  exact le_mul_of_one_le_right' h

theorem exists_v_between {a b : K} (ha : a ≠ 0) (h : 𝓋 a < 𝓋 b) : ∃ s : K, s ≠ 0 ∧ 𝓋 a < 𝓋 s ∧ 𝓋 s < 𝓋 b := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (a * b)
  have hva : 0 < 𝓋 a := (Valuation.pos_iff _).mpr ha
  have hvs : 𝓋 s * 𝓋 s = 𝓋 a * 𝓋 b := by rw [← Valuation.map_mul, ← Valuation.map_mul, hs]
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact (mul_ne_zero ha (fun hb => by rw [hb, Valuation.map_zero] at h; exact (not_lt.mpr zero_le') h)) hs
  have hvb : 0 < 𝓋 b := lt_of_le_of_lt zero_le' h
  refine ⟨s, hs0, ?_, ?_⟩
  · by_contra hle; push_neg at hle
    have h2 : 𝓋 s * 𝓋 s ≤ 𝓋 a * 𝓋 a := mul_le_mul' hle hle
    rw [hvs] at h2
    have h3 := mul_le_mul_right h2 (𝓋 a)⁻¹
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hva.ne', one_mul, one_mul] at h3
    exact absurd h (not_lt.mpr h3)
  · by_contra hle; push_neg at hle
    have h2 : 𝓋 b * 𝓋 b ≤ 𝓋 s * 𝓋 s := mul_le_mul' hle hle
    rw [hvs, mul_comm (𝓋 a)] at h2
    have h3 := mul_le_mul_right h2 (𝓋 b)⁻¹
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hvb.ne', one_mul, one_mul] at h3
    exact absurd h (not_lt.mpr h3)

end Generic

section Tube

variable {c₀ R₀ : K} {H : Finset K} {ρ : K → K} {P : Set K}

theorem mem_of_sphere_generic
    (hP : ∀ z : K, z ∈ P ↔ 𝓋 (z - c₀) ≤ 𝓋 R₀ ∧ ∀ h ∈ H, 𝓋 (ρ h) ≤ 𝓋 (z - h))
    {e r : K} (hsub : ∀ z : K, 𝓋 (z - e) ≤ 𝓋 r → 𝓋 (z - c₀) ≤ 𝓋 R₀)
    {z₁ : K} (hz₁ : z₁ ∈ P) (hz₁e : 𝓋 (z₁ - e) ≤ 𝓋 r)
    {z : K} (hz : 𝓋 (z - e) = 𝓋 r) (hgen : ∀ h ∈ H, 𝓋 r ≤ 𝓋 (z - h)) : z ∈ P := by
  rw [hP]
  refine ⟨hsub z hz.le, fun h hh => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h1 : 𝓋 (e - h) < 𝓋 (ρ h) := by
    calc 𝓋 (e - h) ≤ max (𝓋 (e - z)) (𝓋 (z - h)) := v_sub_le_max e z h
      _ ≤ 𝓋 (z - h) := by rw [v_sub_comm, hz]; exact max_le (hgen h hh) le_rfl
      _ < 𝓋 (ρ h) := hlt
  have h2 : 𝓋 (z₁ - h) < 𝓋 (ρ h) := by
    calc 𝓋 (z₁ - h) ≤ max (𝓋 (z₁ - e)) (𝓋 (e - h)) := v_sub_le_max z₁ e h
      _ < 𝓋 (ρ h) := max_lt (lt_of_le_of_lt (hz₁e.trans (hgen h hh)) hlt) h1
  exact absurd (((hP z₁).mp hz₁).2 h hh) (not_le.mpr h2)

variable [IsAlgClosed K]

theorem no_proper_cover
    (hP : ∀ z : K, z ∈ P ↔ 𝓋 (z - c₀) ≤ 𝓋 R₀ ∧ ∀ h ∈ H, 𝓋 (ρ h) ≤ 𝓋 (z - h))
    {z₀ : K} (hz₀ : z₀ ∈ P) (b : K) (hb : b ≠ 0) (hbR : 𝓋 b ≤ 𝓋 R₀)
    (I : Finset (K × K)) (hI0 : ∀ er ∈ I, er.2 ≠ 0) (hI : ∀ er ∈ I, 𝓋 er.2 < 𝓋 b)
    (hcov : ∀ z ∈ P, 𝓋 (z - z₀) < 𝓋 b → ∃ er ∈ I, 𝓋 (z - er.1) ≤ 𝓋 er.2) : False := by
  classical
  by_cases hIe : I = ∅
  · obtain ⟨er, her, -⟩ := hcov z₀ hz₀ (by rw [sub_self, Valuation.map_zero]; exact (Valuation.pos_iff _).mpr hb)
    simp [hIe] at her
  obtain ⟨erm, herm, hmax⟩ := Finset.exists_max_image I (fun er => 𝓋 er.2) (Finset.nonempty_of_ne_empty hIe)
  obtain ⟨s, hs0, has, hsb⟩ := exists_v_between (K := K) (hI0 erm herm) (hI erm herm)
  obtain ⟨z, hzs, hgen⟩ := exists_generic (K := K) z₀ s hs0 (H ∪ I.image Prod.fst)

  have hzP : z ∈ P := by
    rw [hP]
    obtain ⟨hz₀c, hz₀H⟩ := (hP z₀).mp hz₀
    refine ⟨?_, fun h hh => ?_⟩
    · calc 𝓋 (z - c₀) ≤ max (𝓋 (z - z₀)) (𝓋 (z₀ - c₀)) := v_sub_le_max z z₀ c₀
        _ ≤ 𝓋 R₀ := max_le (by rw [hzs]; exact hsb.le.trans hbR) hz₀c
    · rcases lt_or_ge (𝓋 s) (𝓋 (z₀ - h)) with hlt | hle
      · rw [v_sub_eq_of_lt (by rw [hzs]; exact hlt)]; exact hz₀H h hh
      · exact ((hz₀H h hh).trans hle).trans (hgen h (Finset.mem_union_left _ hh))

  obtain ⟨er, her, hzer⟩ := hcov z hzP (by rw [hzs]; exact hsb)
  have h1 : 𝓋 s ≤ 𝓋 (z - er.1) := hgen er.1 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her))
  have h2 : 𝓋 (z - er.1) < 𝓋 s := lt_of_le_of_lt (hzer.trans (hmax er her)) has
  exact absurd h1 (not_le.mpr h2)

end Tube

section Vacuity

theorem exists_v_eq_one_forall_le_v_sub
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (B : Finset K) : ∃ u : K, Valued.v u = 1 ∧ ∀ b ∈ B, 1 ≤ Valued.v (u - b) :=
  exists_unit_generic B

theorem exists_mem_tube_forall_lt_v_sub
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (z₀ : K) (hz₀ : Valued.v (z₀ - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z₀ - h))
    (U : Finset (K × K)) (hU : ∀ er ∈ U, er.2 ≠ 0)
    (hUnot : ∀ er ∈ U, ¬ (Valued.v (c₀ - er.1) ≤ Valued.v er.2 ∧ Valued.v R₀ ≤ Valued.v er.2)) :
    ∃ z : K, (Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)) ∧
      ∀ er ∈ U, Valued.v er.2 < Valued.v (z - er.1) := by
  classical

  obtain ⟨z, hzs, hgen⟩ := exists_generic (K := K) c₀ R₀ hR₀ (H ∪ U.image Prod.fst)
  refine ⟨z, ⟨hzs.le, fun h hh => ?_⟩, fun er her => ?_⟩
  · have hg := hgen h (Finset.mem_union_left _ hh)
    rcases le_or_gt (Valued.v (ρ h)) (Valued.v R₀) with hle | hlt
    · exact hle.trans hg
    ·
      have h1 : Valued.v R₀ < Valued.v (z₀ - h) := lt_of_lt_of_le hlt (hz₀.2 h hh)
      have h2 : Valued.v (z - z₀) < Valued.v (z₀ - h) :=
        lt_of_le_of_lt ((v_sub_le_max z c₀ z₀).trans (max_le hzs.le (by rw [v_sub_comm]; exact hz₀.1))) h1
      rw [v_sub_eq_of_lt h2]; exact hz₀.2 h hh
  · have hg := hgen er.1 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her))
    rcases lt_or_ge (Valued.v er.2) (Valued.v R₀) with hlt | hle
    · exact lt_of_lt_of_le hlt hg
    · have h1 : Valued.v er.2 < Valued.v (c₀ - er.1) := by
        by_contra h; push_neg at h; exact hUnot er her ⟨h, hle⟩
      have h2 : Valued.v (z - c₀) < Valued.v (c₀ - er.1) := by rw [hzs]; exact lt_of_le_of_lt hle h1
      rw [v_sub_eq_of_lt h2]; exact h1

theorem exists_mem_tube_openDisc_forall_lt_v_sub
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (c₀ R₀ : K) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (e r : K) (hr : r ≠ 0) (hDsub : ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀)
    (z₀ : K) (hz₀ : Valued.v (z₀ - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z₀ - h))
    (hz₀e : Valued.v (z₀ - e) < Valued.v r)
    (U : Finset (K × K)) (hU : ∀ er ∈ U, er.2 ≠ 0)
    (hUnot : ∀ er ∈ U, ¬ (Valued.v (e - er.1) ≤ Valued.v er.2 ∧ Valued.v r ≤ Valued.v er.2)) :
    ∃ z : K, (Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)) ∧
      Valued.v (z - e) < Valued.v r ∧ ∀ er ∈ U, Valued.v er.2 < Valued.v (z - er.1) := by
  classical

  have hfar : ∀ er ∈ U, Valued.v r ≤ Valued.v er.2 → Valued.v er.2 < Valued.v (e - er.1) := by
    intro er her hle
    by_contra h; push_neg at h; exact hUnot er her ⟨h, hle⟩

  set P : Set K := {z | Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)} with hPdef
  have hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h) := fun z => Iff.rfl

  let I := U.filter fun er => Valued.v er.2 < Valued.v r
  by_cases hIe : I = ∅
  ·
    refine ⟨z₀, hz₀, hz₀e, fun er her => ?_⟩
    have hbig : Valued.v r ≤ Valued.v er.2 := by
      by_contra h; push_neg at h
      have : er ∈ I := Finset.mem_filter.mpr ⟨her, h⟩
      rw [hIe] at this; simp at this
    have h1 := hfar er her hbig
    have h2 : Valued.v (z₀ - e) < Valued.v (e - er.1) := lt_of_lt_of_le hz₀e (hbig.trans h1.le)
    rw [v_sub_eq_of_lt h2]; exact h1

  obtain ⟨erm, herm, hmax⟩ := Finset.exists_max_image I (fun er => Valued.v er.2) (Finset.nonempty_of_ne_empty hIe)
  have herm' := Finset.mem_filter.mp herm
  obtain ⟨ℓ, hℓ0, hℓr, hℓz₀, hℓI⟩ : ∃ ℓ : K, ℓ ≠ 0 ∧ Valued.v ℓ < Valued.v r ∧ Valued.v (z₀ - e) ≤ Valued.v ℓ ∧ ∀ er ∈ I, Valued.v er.2 ≤ Valued.v ℓ := by
    rcases le_or_gt (Valued.v (z₀ - e)) (Valued.v erm.2) with hle | hlt
    · exact ⟨erm.2, hU erm herm'.1, herm'.2, hle, hmax⟩
    · refine ⟨z₀ - e, fun h0 => ?_, hz₀e, le_rfl, fun er her => (hmax er her).trans hlt.le⟩
      rw [h0, Valuation.map_zero] at hlt; exact (not_lt.mpr zero_le') hlt
  obtain ⟨s, hs0, hℓs, hsr⟩ := exists_v_between (K := K) hℓ0 hℓr
  obtain ⟨z, hzs, hgen⟩ := exists_generic (K := K) e s hs0 (H ∪ U.image Prod.fst)
  have hzP : z ∈ P :=
    mem_of_sphere_generic hP (fun w hw => hDsub w (hw.trans hsr.le)) (show z₀ ∈ P from hz₀) (hℓz₀.trans hℓs.le) hzs
      (fun h hh => hgen h (Finset.mem_union_left _ hh))
  refine ⟨z, hzP, by rw [hzs]; exact hsr, fun er her => ?_⟩
  have hg := hgen er.1 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ her))
  rcases lt_or_ge (Valued.v er.2) (Valued.v r) with hlt | hle
  · have : er ∈ I := Finset.mem_filter.mpr ⟨her, hlt⟩
    exact lt_of_lt_of_le (lt_of_le_of_lt (hℓI er this) hℓs) hg
  · have h1 := hfar er her hle
    have h2 : Valued.v (z - e) < Valued.v (e - er.1) := by rw [hzs]; exact lt_of_lt_of_le hsr (hle.trans h1.le)
    rw [v_sub_eq_of_lt h2]; exact h1

end Vacuity

end B9

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def tube (c₀ R₀ : K) (H : Finset K) (ρ : K → K) (z : K) : Prop :=
  Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)

def sat (p : Finset (K × K) × Finset (K × K)) (z : K) : Prop :=
  (∀ er ∈ p.1, Valued.v er.2 ≤ Valued.v (z - er.1)) ∧ (∀ er ∈ p.2, Valued.v (z - er.1) ≤ Valued.v er.2)

def weight (s : Finset (Finset (K × K) × Finset (K × K))) : ℕ := s.sum fun p => p.1.card + p.2.card

section Mono
variable (K)

theorem mem_holOn_restrict {S S' : Set K} (hsub : S' ⊆ S) {f : ↥S → K} (hf : f ∈ holOn K S) :
    (fun z : ↥S' => f ⟨(z : K), hsub z.2⟩) ∈ holOn K S' := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hsub hz), ⟨b, fun k z => hb k ⟨(z : K), hsub z.2⟩⟩, ?_⟩
  exact hlim.comp (fun z : ↥S' => (⟨(z : K), hsub z.2⟩ : ↥S))

end Mono

section Geometry

theorem v_sub_comm (a b : K) : Valued.v (a - b) = Valued.v (b - a) := by
  rw [← Valuation.map_neg, neg_sub]

theorem v_sub_le_max (a b c : K) : Valued.v (a - c) ≤ max (Valued.v (a - b)) (Valued.v (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact Valuation.map_add _ _ _

theorem tube_of_sphere_generic {c₀ R₀ : K} {H : Finset K} {ρ : K → K} {e r : K}
    (hsub : ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀)
    {z₀ : K} (hz₀ : tube c₀ R₀ H ρ z₀) (hz₀e : Valued.v (z₀ - e) ≤ Valued.v r)
    {z : K} (hz : Valued.v (z - e) = Valued.v r) (hgen : ∀ h ∈ H, Valued.v r ≤ Valued.v (z - h)) :
    tube c₀ R₀ H ρ z := by
  refine ⟨hsub z hz.le, fun h hh => ?_⟩
  by_contra hlt
  push Not at hlt

  have h1 : Valued.v (e - h) < Valued.v (ρ h) := by
    calc Valued.v (e - h) ≤ max (Valued.v (e - z)) (Valued.v (z - h)) := v_sub_le_max e z h
      _ ≤ Valued.v (z - h) := by rw [v_sub_comm, hz]; exact max_le (hgen h hh) le_rfl
      _ < Valued.v (ρ h) := hlt
  have h2 : Valued.v (z₀ - h) < Valued.v (ρ h) := by
    calc Valued.v (z₀ - h) ≤ max (Valued.v (z₀ - e)) (Valued.v (e - h)) := v_sub_le_max z₀ e h
      _ < Valued.v (ρ h) := max_lt (lt_of_le_of_lt (hz₀e.trans (hgen h hh)) hlt) h1
  exact absurd (hz₀.2 h hh) (not_le.2 h2)

theorem v_sub_le_of_not_sub {c₀ R₀ : K} {H : Finset K} {ρ : K → K} {e r : K}
    (hnot : ¬ ∀ z : K, Valued.v (z - e) ≤ Valued.v r → Valued.v (z - c₀) ≤ Valued.v R₀)
    {z₀ : K} (hz₀ : tube c₀ R₀ H ρ z₀) (hz₀e : Valued.v (z₀ - e) ≤ Valued.v r) :
    Valued.v R₀ < Valued.v r ∧ ∀ z : K, Valued.v (z - c₀) ≤ Valued.v R₀ →
      Valued.v (z - z₀) < Valued.v r := by
  push Not at hnot
  obtain ⟨w, hwe, hwc⟩ := hnot
  have hRr : Valued.v R₀ < Valued.v r := by
    have := v_sub_le_max w z₀ c₀
    have h2 : Valued.v (w - z₀) ≤ Valued.v r :=
      (v_sub_le_max w e z₀).trans (max_le hwe (by rw [v_sub_comm]; exact hz₀e))
    rcases le_max_iff.1 this with h | h
    ·
      by_contra hle; push Not at hle
      exact absurd (hwc.trans_le (h.trans (h2.trans hle))) (lt_irrefl _)
    · exact absurd (hwc.trans_le (h.trans hz₀.1)) (lt_irrefl _)
  refine ⟨hRr, fun z hz => ?_⟩
  calc Valued.v (z - z₀) ≤ max (Valued.v (z - c₀)) (Valued.v (c₀ - z₀)) := v_sub_le_max z c₀ z₀
    _ ≤ Valued.v R₀ := max_le hz (by rw [v_sub_comm]; exact hz₀.1)
    _ < Valued.v r := hRr

end Geometry

section Main
variable (K) [IsAlgClosed K]

theorem mem_holOn_of_empty {S : Set K} (hS : ∀ z : K, z ∉ S) (F : ↥S → K) : F ∈ holOn K S := by
  refine ⟨fun _ => RatPair.const 0, fun k z hz => (hS z hz).elim, ⟨0, fun k z => (hS z.1 z.2).elim⟩, ?_⟩
  intro u hu
  exact Filter.Eventually.of_forall fun n z => (hS z.1 z.2).elim

theorem main (n : ℕ) : ∀ (c₀ R₀ : K) (_hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (_hρ : ∀ h ∈ H, ρ h ≠ 0)
    (U Λ : Finset (K × K)) (_hn : U.card + Λ.card ≤ n)
    (_hU : ∀ er ∈ U, er.2 ≠ 0) (_hΛ : ∀ er ∈ Λ, er.2 ≠ 0)
    (_hcov : ∀ z : K, tube c₀ R₀ H ρ z →
      (∃ er ∈ U, Valued.v (z - er.1) ≤ Valued.v er.2) ∨ (∃ er ∈ Λ, Valued.v er.2 ≤ Valued.v (z - er.1)))
    (F : ↥{z : K | tube c₀ R₀ H ρ z} → K)
    (_hFU : ∀ er ∈ U, (fun z : ↥{z : K | tube c₀ R₀ H ρ z ∧ Valued.v (z - er.1) ≤ Valued.v er.2} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | tube c₀ R₀ H ρ z ∧ Valued.v (z - er.1) ≤ Valued.v er.2})
    (_hFΛ : ∀ er ∈ Λ, (fun z : ↥{z : K | tube c₀ R₀ H ρ z ∧ Valued.v er.2 ≤ Valued.v (z - er.1)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | tube c₀ R₀ H ρ z ∧ Valued.v er.2 ≤ Valued.v (z - er.1)}),
    F ∈ holOn K {z : K | tube c₀ R₀ H ρ z} := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro c₀ R₀ hR₀ H ρ hρ U Λ hn hU hΛ hcov F hFU hFΛ

  by_cases hA : ∃ er ∈ U, ∀ z : K, tube c₀ R₀ H ρ z → Valued.v (z - er.1) ≤ Valued.v er.2
  · obtain ⟨er, her, hall⟩ := hA
    have hsub : {z : K | tube c₀ R₀ H ρ z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ Valued.v (z - er.1) ≤ Valued.v er.2} :=
      fun z hz => ⟨hz, hall z hz⟩
    exact mem_holOn_restrict K hsub (hFU er her)
  by_cases hA' : ∃ er ∈ Λ, ∀ z : K, tube c₀ R₀ H ρ z → Valued.v er.2 ≤ Valued.v (z - er.1)
  · obtain ⟨er, her, hall⟩ := hA'
    have hsub : {z : K | tube c₀ R₀ H ρ z} ⊆ {z : K | tube c₀ R₀ H ρ z ∧ Valued.v er.2 ≤ Valued.v (z - er.1)} :=
      fun z hz => ⟨hz, hall z hz⟩
    exact mem_holOn_restrict K hsub (hFΛ er her)

  by_cases hB : ∃ er ∈ U, ∀ z : K, tube c₀ R₀ H ρ z → Valued.v er.2 < Valued.v (z - er.1)
  · obtain ⟨er, her, hall⟩ := hB
    have hlt : (U.erase er).card + Λ.card < n := by
      have := Finset.card_erase_lt_of_mem her; omega
    refine ih _ hlt c₀ R₀ hR₀ H ρ hρ (U.erase er) Λ le_rfl (fun x hx => hU x (Finset.mem_of_mem_erase hx)) hΛ ?_ F
      (fun x hx => hFU x (Finset.mem_of_mem_erase hx)) hFΛ
    intro z hz
    rcases hcov z hz with ⟨x, hx, hxz⟩ | h
    · refine Or.inl ⟨x, Finset.mem_erase.2 ⟨?_, hx⟩, hxz⟩
      rintro rfl; exact absurd hxz (not_le.2 (hall z hz))
    · exact Or.inr h
  by_cases hB' : ∃ er ∈ Λ, ∀ z : K, tube c₀ R₀ H ρ z → Valued.v (z - er.1) < Valued.v er.2
  · obtain ⟨er, her, hall⟩ := hB'
    have hlt : U.card + (Λ.erase er).card < n := by
      have := Finset.card_erase_lt_of_mem her; omega
    refine ih _ hlt c₀ R₀ hR₀ H ρ hρ U (Λ.erase er) le_rfl hU (fun x hx => hΛ x (Finset.mem_of_mem_erase hx)) ?_ F hFU
      (fun x hx => hFΛ x (Finset.mem_of_mem_erase hx))
    intro z hz
    rcases hcov z hz with h | ⟨x, hx, hxz⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, Finset.mem_erase.2 ⟨?_, hx⟩, hxz⟩
      rintro rfl; exact absurd hxz (not_le.2 (hall z hz))
  push Not at hA hA' hB hB'

  have hDsubΛ : ∀ er ∈ Λ, ∀ z : K, Valued.v (z - er.1) ≤ Valued.v er.2 → Valued.v (z - c₀) ≤ Valued.v R₀ := by
    intro er her
    obtain ⟨z₀, hz₀, hz₀e⟩ := hA' er her
    obtain ⟨z₁, hz₁, hz₁e⟩ := hB' er her
    by_contra hnot
    obtain ⟨-, hall⟩ := v_sub_le_of_not_sub hnot hz₀ hz₀e.le
    exact absurd hz₁e (not_le.2 (lt_of_le_of_lt (v_sub_le_max z₁ z₀ er.1) (max_lt (hall z₁ hz₁.1) hz₀e)))

  by_cases hC1 : ∃ a ∈ Λ, ∃ b ∈ Λ, a ≠ b ∧ (Valued.v (a.1 - b.1) < Valued.v b.2 ∧ Valued.v a.2 ≤ Valued.v b.2)
  · obtain ⟨a, ha, b, hb, hab, hnest⟩ := hC1
    have hlt : U.card + (Λ.erase b).card < n := by
      have := Finset.card_erase_lt_of_mem hb; omega
    refine ih _ hlt c₀ R₀ hR₀ H ρ hρ U (Λ.erase b) le_rfl hU (fun x hx => hΛ x (Finset.mem_of_mem_erase hx)) ?_ F hFU
      (fun x hx => hFΛ x (Finset.mem_of_mem_erase hx))
    intro z hz
    rcases hcov z hz with h | ⟨x, hx, hxz⟩
    · exact Or.inl h
    · by_cases hxb : x = b
      · subst hxb
        refine Or.inr ⟨a, Finset.mem_erase.2 ⟨hab, ha⟩, ?_⟩
        by_contra hlt'
        push Not at hlt'
        have : Valued.v (z - x.1) < Valued.v x.2 :=
          lt_of_le_of_lt (v_sub_le_max z a.1 x.1) (max_lt (lt_of_lt_of_le hlt' hnest.2) hnest.1)
        exact absurd hxz (not_le.2 this)
      · exact Or.inr ⟨x, Finset.mem_erase.2 ⟨hxb, hx⟩, hxz⟩
  by_cases hC1' : ∃ a ∈ U, ∃ b ∈ U, a ≠ b ∧ (Valued.v (a.1 - b.1) ≤ Valued.v b.2 ∧ Valued.v a.2 ≤ Valued.v b.2)
  · obtain ⟨a, ha, b, hb, hab, hnest⟩ := hC1'
    have hlt : (U.erase a).card + Λ.card < n := by
      have := Finset.card_erase_lt_of_mem ha; omega
    refine ih _ hlt c₀ R₀ hR₀ H ρ hρ (U.erase a) Λ le_rfl (fun x hx => hU x (Finset.mem_of_mem_erase hx)) hΛ ?_ F
      (fun x hx => hFU x (Finset.mem_of_mem_erase hx)) hFΛ
    intro z hz
    rcases hcov z hz with ⟨x, hx, hxz⟩ | h
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inl ⟨b, Finset.mem_erase.2 ⟨hab.symm, hb⟩, (v_sub_le_max z x.1 b.1).trans (max_le (hxz.trans hnest.2) hnest.1)⟩
      · exact Or.inl ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩, hxz⟩
    · exact Or.inr h
  push Not at hC1 hC1'

  by_cases hC2 : ∃ a ∈ Λ, ∃ b ∈ Λ, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hC2
    have hna := hC1 a ha b hb hab
    have hnb := hC1 b hb a ha hab.symm
    obtain ⟨z₀, hz₀, hz₀e⟩ := hA' a ha
    have hDsub := hDsubΛ a ha
    have hra : a.2 ≠ 0 := hΛ a ha
    set S₁ : Set K := {z : K | tube c₀ R₀ H ρ z ∧ Valued.v a.2 ≤ Valued.v (z - a.1)} with hS₁
    set S₂ : Set K := {z : K | tube c₀ R₀ H ρ z ∧ Valued.v b.2 ≤ Valued.v (z - b.1)} with hS₂
    have hUsub : ∀ z : K, z ∈ S₁ ∪ S₂ → tube c₀ R₀ H ρ z := fun z hz => hz.elim (fun h => h.1) (fun h => h.1)
    have hglue := CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt K S₁ S₂ a.1 a.2 hra
      (insert b.1 H)
      (fun z hz => hz.2)
      (fun z hz => by
        rcases le_or_gt (Valued.v a.2) (Valued.v (z - a.1)) with h | h
        · exact Or.inl ⟨hz.1, h⟩
        · exact Or.inr h)
      (fun z hz hgen => by
        have ht : tube c₀ R₀ H ρ z :=
          tube_of_sphere_generic hDsub hz₀ hz₀e.le hz (fun h hh => hgen h (Finset.mem_insert_of_mem hh))
        refine ⟨⟨ht, hz.ge⟩, ⟨ht, ?_⟩⟩
        have hgb : Valued.v a.2 ≤ Valued.v (z - b.1) := hgen b.1 (Finset.mem_insert_self _ _)
        rcases le_or_gt (Valued.v b.2) (Valued.v a.2) with hba | hba
        · exact hba.trans hgb
        ·
          have hfar : Valued.v b.2 ≤ Valued.v (a.1 - b.1) := not_lt.1 fun hlt => absurd (hna hlt) (not_lt.2 hba.le)
          have heq : Valued.v (z - b.1) = Valued.v (a.1 - b.1) := by
            have : z - b.1 = (a.1 - b.1) + (z - a.1) := by ring
            rw [this]
            exact Valuation.map_add_eq_of_lt_left _ (by rw [hz]; exact lt_of_lt_of_le hba hfar)
          rw [heq]; exact hfar)
      (fun z => F ⟨(z : K), hUsub z z.2⟩) (hFΛ a ha) (hFΛ b hb)
    have hsub : {z : K | tube c₀ R₀ H ρ z} ⊆ S₁ ∪ S₂ := by
      intro z hz
      rcases le_or_gt (Valued.v a.2) (Valued.v (z - a.1)) with h | h
      · exact Or.inl ⟨hz, h⟩
      rcases le_or_gt (Valued.v b.2) (Valued.v (z - b.1)) with h' | h'
      · exact Or.inr ⟨hz, h'⟩

      exfalso
      rcases le_total (Valued.v a.2) (Valued.v b.2) with hab' | hab'
      · exact absurd (hna (lt_of_le_of_lt (v_sub_le_max a.1 z b.1)
          (max_lt (by rw [v_sub_comm]; exact lt_of_lt_of_le h hab') h'))) (not_lt.2 hab')
      · exact absurd (hnb (lt_of_le_of_lt (v_sub_le_max b.1 z a.1)
          (max_lt (by rw [v_sub_comm]; exact lt_of_lt_of_le h' hab') h))) (not_lt.2 hab')
    exact mem_holOn_restrict K hsub hglue
  push Not at hC2

  by_cases hΛe : Λ = ∅
  ·
    by_cases hP : ∃ z₀ : K, tube c₀ R₀ H ρ z₀
    · obtain ⟨z₀, hz₀⟩ := hP
      exfalso
      have hUnot : ∀ er ∈ U, ¬ (Valued.v (c₀ - er.1) ≤ Valued.v er.2 ∧ Valued.v R₀ ≤ Valued.v er.2) := by
        intro er her hcon
        obtain ⟨z₁, hz₁, hz₁e⟩ := hA er her
        exact absurd hz₁e (not_lt.2 ((v_sub_le_max z₁ c₀ er.1).trans (max_le (hz₁.1.trans hcon.2) hcon.1)))
      obtain ⟨z, hz, hfar⟩ := B9.exists_mem_tube_forall_lt_v_sub K c₀ R₀ hR₀ H ρ hρ z₀ hz₀ U hU hUnot
      rcases hcov z hz with ⟨x, hx, hxz⟩ | ⟨x, hx, -⟩
      · exact absurd hxz (not_le.2 (hfar x hx))
      · rw [hΛe] at hx; exact absurd hx (Finset.notMem_empty _)
    · push Not at hP
      exact mem_holOn_of_empty K (fun z hz => hP z hz) F
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hΛe
    have hΛa : ∀ x ∈ Λ, x = a := fun x hx => hC2 x hx a ha
    obtain ⟨z₀, hz₀, hz₀e⟩ := hA' a ha
    have hDsub := hDsubΛ a ha
    have hra : a.2 ≠ 0 := hΛ a ha
    by_cases hC3 : ∃ er ∈ U, Valued.v (a.1 - er.1) ≤ Valued.v er.2 ∧ Valued.v a.2 ≤ Valued.v er.2
    ·
      obtain ⟨er, her, hcon⟩ := hC3
      set S₁ : Set K := {z : K | tube c₀ R₀ H ρ z ∧ Valued.v a.2 ≤ Valued.v (z - a.1)} with hS₁
      set S₂ : Set K := {z : K | tube c₀ R₀ H ρ z ∧ Valued.v (z - er.1) ≤ Valued.v er.2} with hS₂
      have hUsub : ∀ z : K, z ∈ S₁ ∪ S₂ → tube c₀ R₀ H ρ z := fun z hz => hz.elim (fun h => h.1) (fun h => h.1)
      have hin : ∀ z : K, Valued.v (z - a.1) ≤ Valued.v a.2 → Valued.v (z - er.1) ≤ Valued.v er.2 := fun z hz =>
        (v_sub_le_max z a.1 er.1).trans (max_le (hz.trans hcon.2) hcon.1)
      have hglue := CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt K S₁ S₂ a.1 a.2 hra H
        (fun z hz => hz.2)
        (fun z hz => by
          rcases le_or_gt (Valued.v a.2) (Valued.v (z - a.1)) with h | h
          · exact Or.inl ⟨hz.1, h⟩
          · exact Or.inr h)
        (fun z hz hgen => by
          have ht : tube c₀ R₀ H ρ z := tube_of_sphere_generic hDsub hz₀ hz₀e.le hz hgen
          exact ⟨⟨ht, hz.ge⟩, ⟨ht, hin z hz.le⟩⟩)
        (fun z => F ⟨(z : K), hUsub z z.2⟩) (hFΛ a ha) (hFU er her)
      have hsub : {z : K | tube c₀ R₀ H ρ z} ⊆ S₁ ∪ S₂ := by
        intro z hz
        rcases le_or_gt (Valued.v a.2) (Valued.v (z - a.1)) with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, hin z h.le⟩
      exact mem_holOn_restrict K hsub hglue
    ·
      push Not at hC3
      exfalso
      obtain ⟨z, hz, hze, hfar⟩ := B9.exists_mem_tube_openDisc_forall_lt_v_sub K c₀ R₀ H ρ hρ a.1 a.2 hra hDsub z₀ hz₀ hz₀e U hU
        (fun er her hcon => absurd hcon.2 (not_le.2 (hC3 er her hcon.1)))
      rcases hcov z hz with ⟨x, hx, hxz⟩ | ⟨x, hx, hxz⟩
      · exact absurd hxz (not_le.2 (hfar x hx))
      · rw [hΛa x hx] at hxz; exact absurd hxz (not_le.2 hze)

end Main

end CerednikDrinfeld.Omega.SHC

open CerednikDrinfeld.Omega.SHC in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]

    (c₀ R₀ : K) (hR₀ : R₀ ≠ 0) (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (P : Set K) (hP : ∀ z : K, z ∈ P ↔ Valued.v (z - c₀) ≤ Valued.v R₀ ∧ ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h))

    (U Λ : Finset (K × K)) (hU : ∀ er ∈ U, er.2 ≠ 0) (hΛ : ∀ er ∈ Λ, er.2 ≠ 0)
    (hcov : ∀ z ∈ P, (∃ er ∈ U, Valued.v (z - er.1) ≤ Valued.v er.2) ∨ (∃ er ∈ Λ, Valued.v er.2 ≤ Valued.v (z - er.1)))

    (F : ↥P → K)
    (hFU : ∀ er ∈ U, (fun z : ↥{z : K | z ∈ P ∧ Valued.v (z - er.1) ≤ Valued.v er.2} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ Valued.v (z - er.1) ≤ Valued.v er.2})
    (hFΛ : ∀ er ∈ Λ, (fun z : ↥{z : K | z ∈ P ∧ Valued.v er.2 ≤ Valued.v (z - er.1)} => F ⟨(z : K), z.2.1⟩) ∈
        holOn K {z : K | z ∈ P ∧ Valued.v er.2 ≤ Valued.v (z - er.1)}) :
    F ∈ holOn K P := by
  classical
  have hPeq : P = {z : K | tube c₀ R₀ H ρ z} := Set.ext fun z => hP z
  subst hPeq
  refine main K (U.card + Λ.card) c₀ R₀ hR₀ H ρ hρ U Λ le_rfl hU hΛ (fun z hz => hcov z hz) F ?_ ?_
  · intro er her
    exact mem_holOn_restrict K (fun z hz => hz) (hFU er her)
  · intro er her
    exact mem_holOn_restrict K (fun z hz => hz) (hFΛ er her)

end

end S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_halfDiscPiece_of_cover (solution)
