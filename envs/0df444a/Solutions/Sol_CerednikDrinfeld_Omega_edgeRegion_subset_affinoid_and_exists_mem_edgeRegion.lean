-- Prove2me | solution 1 for CerednikDrinfeld.Omega.edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/08afb890-027f-5232-8591-320748385d26

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace L3Aux

variable (K₀ : Type) [Field K₀] {C : Type} [Field C] [Algebra K₀ C]

def aff (c : K₀ˣ) (a : K₀) : GL (Fin 2) K₀ :=
  ⟨!![(c : K₀), a; 0, 1], !![((c⁻¹ : K₀ˣ) : K₀), -(((c⁻¹ : K₀ˣ) : K₀) * a); 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem aff_apply_00 (c : K₀ˣ) (a : K₀) : (aff K₀ c a : GL (Fin 2) K₀) 0 0 = c := rfl
theorem aff_apply_01 (c : K₀ˣ) (a : K₀) : (aff K₀ c a : GL (Fin 2) K₀) 0 1 = a := rfl
theorem aff_apply_10 (c : K₀ˣ) (a : K₀) : (aff K₀ c a : GL (Fin 2) K₀) 1 0 = 0 := rfl
theorem aff_apply_11 (c : K₀ˣ) (a : K₀) : (aff K₀ c a : GL (Fin 2) K₀) 1 1 = 1 := rfl
theorem aff_inv_apply_00 (c : K₀ˣ) (a : K₀) : ((aff K₀ c a)⁻¹ : GL (Fin 2) K₀) 0 0 = ((c⁻¹ : K₀ˣ) : K₀) := rfl
theorem aff_inv_apply_01 (c : K₀ˣ) (a : K₀) : ((aff K₀ c a)⁻¹ : GL (Fin 2) K₀) 0 1 = -(((c⁻¹ : K₀ˣ) : K₀) * a) := rfl
theorem aff_inv_apply_10 (c : K₀ˣ) (a : K₀) : ((aff K₀ c a)⁻¹ : GL (Fin 2) K₀) 1 0 = 0 := rfl
theorem aff_inv_apply_11 (c : K₀ˣ) (a : K₀) : ((aff K₀ c a)⁻¹ : GL (Fin 2) K₀) 1 1 = 1 := rfl

variable [DecidableEq C]

theorem pmoebius_aff (c : K₀ˣ) (a : K₀) (z : C) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (aff K₀ c a)) z = algebraMap K₀ C c * z + algebraMap K₀ C a := by
  rw [pmoebius_mk K₀ (aff K₀ c a) z (by rw [aff_apply_10, aff_apply_11, map_zero, zero_mul, zero_add, map_one]; exact one_ne_zero),
    moebius, aff_apply_00, aff_apply_01, aff_apply_10, aff_apply_11, map_zero, map_one, zero_mul, zero_add, div_one]

theorem pmoebius_aff_inv (c : K₀ˣ) (a : K₀) (z : C) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (aff K₀ c a))⁻¹ z = (z - algebraMap K₀ C a) / algebraMap K₀ C c := by
  have hc : algebraMap K₀ C (c : K₀) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact c.ne_zero
  rw [← map_inv, pmoebius_mk K₀ (aff K₀ c a)⁻¹ z (by rw [aff_inv_apply_10, aff_inv_apply_11, map_zero, zero_mul, zero_add, map_one]; exact one_ne_zero),
    moebius, aff_inv_apply_00, aff_inv_apply_01, aff_inv_apply_10, aff_inv_apply_11, map_zero, map_one, zero_mul,
    zero_add, div_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  field_simp
  ring

theorem aff_mul_edgeFlip {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] (ϖ : PseudoUniformizer K₀ C)
    (c : K₀ˣ) (a : K₀) :
    aff K₀ c a * FormalOmega.edgeFlip K₀ ϖ = aff K₀ (c * Units.mk0 ϖ.ϖ (FormalOmega.edgeFlip_ne_zero K₀ ϖ)) a := by
  apply Units.ext
  show (!![(c : K₀), a; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) * Matrix.diagonal ![ϖ.ϖ, (1 : K₀)] = !![(c : K₀) * ϖ.ϖ, a; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

section Core

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] (ϖ : PseudoUniformizer K₀ C)

abbrev wu : K₀ˣ := Units.mk0 ϖ.ϖ (FormalOmega.edgeFlip_ne_zero K₀ ϖ)

theorem algebraMap_wu_zpow (m : ℤ) :
    algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) = (algebraMap K₀ C ϖ.ϖ) ^ m := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]; rfl

theorem v_wu_zpow (m : ℤ) :
    Valued.v (algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀)) = (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ m := by
  rw [algebraMap_wu_zpow, map_zpow₀]

theorem mem_vertexTube_aff_iff (c : K₀ˣ) (a : K₀) (z : C) :
    z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ c a)) ↔
      z ∈ upperHalfPlane K₀ C ∧ (z - algebraMap K₀ C a) / algebraMap K₀ C c ∈ affinoid ϖ 0 := by
  rw [mem_vertexTube_iff, pmoebius_aff_inv]

theorem mem_edgeTube_aff_iff (c : K₀ˣ) (a : K₀) (z : C) :
    z ∈ edgeTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ c a)) ↔
      z ∈ upperHalfPlane K₀ C ∧ (z - algebraMap K₀ C a) / algebraMap K₀ C c ∈ stdEdgeTube ϖ := by
  rw [mem_edgeTube_iff, pmoebius_aff_inv]

theorem mem_vertexTube_aff_mul_edgeFlip_iff (c : K₀ˣ) (a : K₀) (z : C) :
    z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ c a * FormalOmega.edgeFlip K₀ ϖ)) ↔
      z ∈ upperHalfPlane K₀ C ∧
        (z - algebraMap K₀ C a) / (algebraMap K₀ C c * algebraMap K₀ C ϖ.ϖ) ∈ affinoid ϖ 0 := by
  rw [aff_mul_edgeFlip, mem_vertexTube_aff_iff]
  simp only [Units.val_mul, Units.val_mk0, map_mul]

theorem exists_mem_edgeRegion_aff (n : ℕ) (hn : 1 ≤ n) (z : C) (hz : z ∈ affinoid ϖ n) :
    ∃ (m : ℤ) (a : K₀), -(n : ℤ) ≤ m ∧ m + 1 ≤ n ∧
      Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n ∧
      z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ (wu K₀ ϖ ^ m) a)) ∪
        edgeTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ (wu K₀ ϖ ^ m) a)) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ (wu K₀ ϖ ^ m) a * FormalOmega.edgeFlip K₀ ϖ)) := by
  classical

  have hρ0 : 0 < Valued.v (algebraMap K₀ C ϖ.ϖ) := ϖ.pos
  have hρ1 : Valued.v (algebraMap K₀ C ϖ.ϖ) < 1 := ϖ.lt_one
  have hρne : Valued.v (algebraMap K₀ C ϖ.ϖ) ≠ 0 := hρ0.ne'
  have hpne : algebraMap K₀ C ϖ.ϖ ≠ 0 := fun h => by rw [h, map_zero] at hρ0; exact lt_irrefl _ hρ0

  have hR_anti : ∀ k l : ℤ, k < l → Valued.v (algebraMap K₀ C ϖ.ϖ) ^ l < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k :=
    fun k l h => zpow_lt_zpow_right_of_lt_one₀ hρ0 hρ1 h
  have hR_le : ∀ k l : ℤ, k ≤ l → Valued.v (algebraMap K₀ C ϖ.ϖ) ^ l ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k := by
    intro k l h
    rcases h.lt_or_eq with h | h
    · exact (hR_anti k l h).le
    · rw [h]
  have hRn : (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n = Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (-(n : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hRn' : (Valued.v (algebraMap K₀ C ϖ.ϖ)) ^ n = Valued.v (algebraMap K₀ C ϖ.ϖ) ^ ((n : ℤ)) := by
    rw [zpow_natCast]
  have hzΩ : z ∈ upperHalfPlane K₀ C := affinoid_subset_upperHalfPlane ϖ n hz
  obtain ⟨hz1, hz2⟩ := hz

  set S : Finset ℤ := (Finset.Icc (-(n : ℤ)) n).filter
    (fun k => ∃ a : K₀, Valued.v (z - algebraMap K₀ C a) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k) with hS
  have hSmem : ∀ k, k ∈ S ↔ (-(n : ℤ) ≤ k ∧ k ≤ n) ∧ ∃ a : K₀, Valued.v (z - algebraMap K₀ C a) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k := by
    intro k; rw [hS, Finset.mem_filter, Finset.mem_Icc]
  have hS0 : (-(n : ℤ)) ∈ S := by
    rw [hSmem]
    refine ⟨⟨le_rfl, by omega⟩, 0, ?_⟩
    rw [map_zero, sub_zero, ← hRn]; exact hz1
  have hSne : S.Nonempty := ⟨_, hS0⟩
  set m : ℤ := S.max' hSne with hm
  have hmS : m ∈ S := Finset.max'_mem S hSne
  have hmax : ∀ k ∈ S, k ≤ m := fun k hk => Finset.le_max' S k hk
  obtain ⟨⟨hmlo, hmhi⟩, a₀, ha₀⟩ := (hSmem m).1 hmS

  have hint : ∀ (a : K₀) (k : ℤ), -(n : ℤ) ≤ k → Valued.v (z - algebraMap K₀ C a) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k →
      Valued.v (algebraMap K₀ C a) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n := by
    intro a k hk h
    rw [hRn]
    have : algebraMap K₀ C a = z - (z - algebraMap K₀ C a) := by ring
    rw [this]
    refine (Valuation.map_sub _ _ _).trans (max_le (by rw [← hRn]; exact hz1) (h.trans (hR_le _ _ hk)))
  have ha₀int := hint a₀ m hmlo ha₀

  have hwv : Valued.v ((z - algebraMap K₀ C a₀) / algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀)) ≤ 1 := by
    rw [map_div₀, v_wu_zpow]
    exact div_le_one_of_le₀ ha₀ zero_le'
  by_cases hgen : ∃ b : K₀, Valued.v (algebraMap K₀ C b) ≤ 1 ∧
      Valued.v ((z - algebraMap K₀ C a₀) / algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) - algebraMap K₀ C b) < 1
  ·
    obtain ⟨b, hb1, hb⟩ := hgen
    set a₁ : K₀ := a₀ + ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) * b with ha₁
    have hza₁ : z - algebraMap K₀ C a₁ = algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) *
        ((z - algebraMap K₀ C a₀) / algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) - algebraMap K₀ C b) := by
      have hne : algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) ≠ 0 := by
        rw [algebraMap_wu_zpow]; exact zpow_ne_zero _ hpne
      rw [ha₁, map_add, map_mul]; field_simp; ring
    have hlt : Valued.v (z - algebraMap K₀ C a₁) < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ m := by
      rw [hza₁, map_mul, v_wu_zpow]
      calc Valued.v (algebraMap K₀ C ϖ.ϖ) ^ m * Valued.v ((z - algebraMap K₀ C a₀) / algebraMap K₀ C ↑(wu K₀ ϖ ^ m) - algebraMap K₀ C b)
          < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ m * 1 := mul_lt_mul_of_pos_left hb (zpow_pos hρ0 m)
        _ = _ := mul_one _
    have ha₁int : Valued.v (algebraMap K₀ C a₁) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n :=
      hint a₁ m hmlo hlt.le

    have hmn : m + 1 ≤ n := by
      by_contra hcon
      have hmeq : m = n := by omega
      have := hz2 a₁ ha₁int
      rw [hRn', ← hmeq] at this
      exact absurd hlt (not_lt.2 this)

    have hlow : Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (m + 1) < Valued.v (z - algebraMap K₀ C a₁) := by
      by_contra hcon
      rw [not_lt] at hcon
      have : m + 1 ∈ S := (hSmem _).2 ⟨⟨by omega, hmn⟩, a₁, hcon⟩
      have := hmax _ this
      omega
    refine ⟨m, a₁, hmlo, hmn, ha₁int, Or.inl (Or.inr ?_)⟩
    rw [mem_edgeTube_aff_iff]
    refine ⟨hzΩ, ?_, ?_, ?_⟩
    · rw [← pmoebius_aff_inv]; exact pmoebius_mem_upperHalfPlane K₀ hzΩ _
    · rw [map_div₀, v_wu_zpow, lt_div_iff₀ (zpow_pos hρ0 m), mul_comm, ← zpow_add_one₀ hρne]
      exact hlow
    · rw [map_div₀, v_wu_zpow, div_lt_one₀ (zpow_pos hρ0 m)]
      exact hlt
  ·
    push Not at hgen
    have hw : (z - algebraMap K₀ C a₀) / algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) ∈ affinoid ϖ 0 := by
      refine ⟨by rw [pow_zero]; exact hwv, fun b hb => ?_⟩
      rw [pow_zero] at hb ⊢
      exact hgen b hb
    have hvT : z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk (aff K₀ (wu K₀ ϖ ^ m) a₀)) := by
      rw [mem_vertexTube_aff_iff]; exact ⟨hzΩ, hw⟩
    by_cases hm0 : m = -(n : ℤ)
    · refine ⟨m, a₀, hmlo, by omega, ha₀int, Or.inl (Or.inl hvT)⟩
    · refine ⟨m - 1, a₀, by omega, by omega, ha₀int, Or.inr ?_⟩
      rw [mem_vertexTube_aff_mul_edgeFlip_iff]
      refine ⟨hzΩ, ?_⟩
      have : algebraMap K₀ C ((wu K₀ ϖ ^ (m - 1) : K₀ˣ) : K₀) * algebraMap K₀ C ϖ.ϖ =
          algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) := by
        rw [algebraMap_wu_zpow, algebraMap_wu_zpow, ← zpow_add_one₀ hpne, sub_add_cancel]
      rw [this]; exact hw

end Core

section Contain

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] (ϖ : PseudoUniformizer K₀ C)

theorem R_antitone {a b : ℤ} (h : a ≤ b) :
    Valued.v (algebraMap K₀ C ϖ.ϖ) ^ b ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ a := by
  rcases h.lt_or_eq with h | h
  · exact (zpow_lt_zpow_right_of_lt_one₀ ϖ.pos ϖ.lt_one h).le
  · rw [h]

theorem inv_pow_eq_zpow_neg (n : ℕ) :
    (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n = Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem mem_affinoid_of_rescale_mem (n : ℕ) (k : ℤ) (hk1 : -(n : ℤ) ≤ k) (hk2 : k ≤ n) (c : K₀)
    (hc : Valued.v (algebraMap K₀ C c) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n) (z : C)
    (hw : (z - algebraMap K₀ C c) / algebraMap K₀ C ((wu K₀ ϖ ^ k : K₀ˣ) : K₀) ∈ affinoid ϖ 0) :
    z ∈ affinoid ϖ n := by
  have hρ0 : 0 < Valued.v (algebraMap K₀ C ϖ.ϖ) := ϖ.pos
  have hpne : algebraMap K₀ C ϖ.ϖ ≠ 0 := fun h => by rw [h, map_zero] at hρ0; exact lt_irrefl _ hρ0
  have hpk : algebraMap K₀ C ((wu K₀ ϖ ^ k : K₀ˣ) : K₀) ≠ 0 := by
    rw [algebraMap_wu_zpow]; exact zpow_ne_zero _ hpne
  obtain ⟨hw1, hw2⟩ := hw
  rw [pow_zero] at hw1
  have hzc : Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k := by
    rw [map_div₀, v_wu_zpow, div_le_one₀ (zpow_pos hρ0 k)] at hw1; exact hw1
  refine ⟨?_, fun a ha => ?_⟩
  · have : z = (z - algebraMap K₀ C c) + algebraMap K₀ C c := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le (hzc.trans ?_) hc)
    rw [inv_pow_eq_zpow_neg]; exact R_antitone K₀ ϖ hk1
  · rw [← zpow_natCast]
    rcases le_or_gt (Valued.v (algebraMap K₀ C a - algebraMap K₀ C c)) (Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k) with h | h
    ·
      have hb : Valued.v (algebraMap K₀ C ((a - c) * ((wu K₀ ϖ ^ k : K₀ˣ) : K₀)⁻¹)) ≤
          (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ 0 := by
        rw [pow_zero, map_mul, map_inv₀, map_sub, map_mul, map_inv₀, v_wu_zpow, ← div_eq_mul_inv,
          div_le_one₀ (zpow_pos hρ0 k)]
        exact h
      have h1 := hw2 _ hb
      rw [pow_zero] at h1
      have heq : (z - algebraMap K₀ C c) / algebraMap K₀ C ↑(wu K₀ ϖ ^ k) - algebraMap K₀ C ((a - c) * (↑(wu K₀ ϖ ^ k))⁻¹) =
          (z - algebraMap K₀ C a) / algebraMap K₀ C ↑(wu K₀ ϖ ^ k) := by
        rw [map_mul, map_inv₀, map_sub]; field_simp; ring
      rw [heq, map_div₀, v_wu_zpow, le_div_iff₀ (zpow_pos hρ0 k), one_mul] at h1
      exact (R_antitone K₀ ϖ hk2).trans h1
    ·
      have hlt : Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C a - algebraMap K₀ C c) := hzc.trans_lt h
      have : z - algebraMap K₀ C a = (z - algebraMap K₀ C c) - (algebraMap K₀ C a - algebraMap K₀ C c) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_right _ hlt]
      exact ((R_antitone K₀ ϖ hk2).trans h.le)

theorem mem_affinoid_of_annulus
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K₀] [IsFractionRing R K₀]
    (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (m : ℤ) (hm1 : 1 - (n : ℤ) ≤ m) (hm2 : m ≤ n) (c : K₀)
    (hc : Valued.v (algebraMap K₀ C c) ≤ (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n) (z : C)
    (h1 : Valued.v (algebraMap K₀ C ϖ.ϖ) ^ m < Valued.v (z - algebraMap K₀ C c))
    (h2 : Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (m - 1)) :
    z ∈ affinoid ϖ n := by
  have hρ0 : 0 < Valued.v (algebraMap K₀ C ϖ.ϖ) := ϖ.pos
  have hpne : algebraMap K₀ C ϖ.ϖ ≠ 0 := fun h => by rw [h, map_zero] at hρ0; exact lt_irrefl _ hρ0

  have hdisc : ∀ (x : K₀) (k : ℤ), Valued.v (algebraMap K₀ C x) < Valued.v (algebraMap K₀ C ϖ.ϖ) ^ k →
      Valued.v (algebraMap K₀ C x) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (k + 1) := by
    intro x k hx
    set y : K₀ := x * (((wu K₀ ϖ ^ k : K₀ˣ) : K₀))⁻¹ with hy
    have hxy : x = y * ((wu K₀ ϖ ^ k : K₀ˣ) : K₀) := by
      rw [hy, inv_mul_cancel_right₀ (Units.ne_zero _)]
    have hvy : Valued.v (algebraMap K₀ C y) < 1 := by
      rw [hy, map_mul, map_inv₀, map_mul, map_inv₀, v_wu_zpow, ← div_eq_mul_inv, div_lt_one₀ (zpow_pos hρ0 k)]
      exact hx
    obtain ⟨r, hr⟩ := hv y hvy.le
    have hru : ¬ IsUnit r := by
      rintro ⟨u, rfl⟩
      have h1 := hint ((u⁻¹ : Rˣ) : R)
      have hprod : Valued.v (algebraMap K₀ C (algebraMap R K₀ (u : R))) *
          Valued.v (algebraMap K₀ C (algebraMap R K₀ ((u⁻¹ : Rˣ) : R))) = 1 := by
        rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
      have hvu : Valued.v (algebraMap K₀ C (algebraMap R K₀ (u : R))) < 1 := by rw [hr]; exact hvy
      have : Valued.v (algebraMap K₀ C (algebraMap R K₀ (u : R))) *
          Valued.v (algebraMap K₀ C (algebraMap R K₀ ((u⁻¹ : Rˣ) : R))) < 1 := mul_lt_one_of_lt_of_le hvu h1
      exact this.ne hprod
    have hmem : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).2 hru
    rw [hϖ₀.maximalIdeal_eq] at hmem
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    have hvy' : Valued.v (algebraMap K₀ C y) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) := by
      rw [← hr, ← hs, map_mul, map_mul, map_mul, ← hϖ]
      calc Valued.v (algebraMap K₀ C (algebraMap R K₀ s)) * Valued.v (algebraMap K₀ C ϖ.ϖ)
          ≤ 1 * Valued.v (algebraMap K₀ C ϖ.ϖ) := mul_le_mul_left (hint s) _
        _ = _ := one_mul _
    have hρne : Valued.v (algebraMap K₀ C ϖ.ϖ) ≠ 0 := hρ0.ne'
    rw [hxy, map_mul, map_mul, v_wu_zpow, zpow_add_one₀ hρne, mul_comm]
    exact mul_le_mul_right hvy' _
  refine ⟨?_, fun a ha => ?_⟩
  · have : z = (z - algebraMap K₀ C c) + algebraMap K₀ C c := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le (h2.le.trans ?_) hc)
    rw [inv_pow_eq_zpow_neg]; exact R_antitone K₀ ϖ (by omega)
  · rw [← zpow_natCast]
    rcases le_or_gt (Valued.v (algebraMap K₀ C ϖ.ϖ) ^ (m - 1)) (Valued.v (algebraMap K₀ C a - algebraMap K₀ C c)) with h | h
    · have hlt : Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C a - algebraMap K₀ C c) := h2.trans_le h
      have : z - algebraMap K₀ C a = (z - algebraMap K₀ C c) - (algebraMap K₀ C a - algebraMap K₀ C c) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_right _ hlt]
      exact (R_antitone K₀ ϖ (by omega : (n : ℤ) ≥ m - 1)).trans h
    · have hle : Valued.v (algebraMap K₀ C a - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C ϖ.ϖ) ^ m := by
        have := hdisc (a - c) (m - 1) (by rw [map_sub]; exact h)
        rwa [sub_add_cancel, map_sub] at this
      have hlt : Valued.v (algebraMap K₀ C a - algebraMap K₀ C c) < Valued.v (z - algebraMap K₀ C c) := hle.trans_lt h1
      have : z - algebraMap K₀ C a = (z - algebraMap K₀ C c) - (algebraMap K₀ C a - algebraMap K₀ C c) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ hlt]
      exact (R_antitone K₀ ϖ hm2).trans h1.le

end Contain

end L3Aux

open L3Aux in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀), (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] →
      1 - (n : ℤ) ≤ m → m ≤ n → Valued.v (algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) →
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ)) ⊆ affinoid ϖ n) ∧
    (∀ z : C, z ∈ affinoid ϖ n → ∃ (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀),
      (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1] ∧ 1 - (n : ℤ) ≤ m ∧ m ≤ n ∧
      Valued.v (algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) ∧
      z ∈ vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
        vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) := by
  classical
  have hρ0 : 0 < Valued.v (algebraMap K₀ C ϖ.ϖ) := ϖ.pos
  have hpne : algebraMap K₀ C ϖ.ϖ ≠ 0 := fun h => by rw [h, map_zero] at hρ0; exact lt_irrefl _ hρ0
  have hRneg : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))) = (Valued.v (algebraMap K₀ C ϖ.ϖ))⁻¹ ^ n := by
    rw [map_zpow₀, map_zpow₀, inv_pow_eq_zpow_neg]
  have hval : ∀ k : ℤ, ((wu K₀ ϖ ^ k : K₀ˣ) : K₀) = ϖ.ϖ ^ k := fun k => by
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  refine ⟨?_, ?_⟩
  · intro c m g hg hm1 hm2 hc
    have hgeq : g = aff K₀ (wu K₀ ϖ ^ (m - 1)) c := by
      apply Units.ext
      rw [hg]
      show (!![ϖ.ϖ ^ (m - 1), c; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) = !![((wu K₀ ϖ ^ (m - 1) : K₀ˣ) : K₀), c; 0, 1]
      rw [hval]
    rw [hRneg] at hc
    subst hgeq
    rintro z ((h | h) | h)
    · obtain ⟨-, hw⟩ := (mem_vertexTube_aff_iff K₀ ϖ _ c z).1 h
      exact mem_affinoid_of_rescale_mem K₀ ϖ n (m - 1) (by omega) (by omega) c hc z hw
    · obtain ⟨-, -, hlo, hhi⟩ := (mem_edgeTube_aff_iff K₀ ϖ _ c z).1 h
      rw [map_div₀, v_wu_zpow, lt_div_iff₀ (zpow_pos hρ0 _), mul_comm, ← zpow_add_one₀ hρ0.ne', sub_add_cancel] at hlo
      rw [map_div₀, v_wu_zpow, div_lt_one₀ (zpow_pos hρ0 _)] at hhi
      exact mem_affinoid_of_annulus K₀ ϖ R ϖ₀ hϖ₀ hϖ hint hv n m hm1 hm2 c hc z hlo hhi
    · obtain ⟨-, hw⟩ := (mem_vertexTube_aff_mul_edgeFlip_iff K₀ ϖ _ c z).1 h
      have : algebraMap K₀ C ((wu K₀ ϖ ^ (m - 1) : K₀ˣ) : K₀) * algebraMap K₀ C ϖ.ϖ =
          algebraMap K₀ C ((wu K₀ ϖ ^ m : K₀ˣ) : K₀) := by
        rw [algebraMap_wu_zpow, algebraMap_wu_zpow, ← zpow_add_one₀ hpne, sub_add_cancel]
      rw [this] at hw
      exact mem_affinoid_of_rescale_mem K₀ ϖ n m (by omega) hm2 c hc z hw
  · intro z hz
    obtain ⟨m, a, hm1, hm2, ha, hmem⟩ := exists_mem_edgeRegion_aff K₀ ϖ n hn z hz
    refine ⟨a, m + 1, aff K₀ (wu K₀ ϖ ^ m) a, ?_, by omega, by omega, ?_, hmem⟩
    · show (!![((wu K₀ ϖ ^ m : K₀ˣ) : K₀), a; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m + 1 - 1), a; 0, 1]
      rw [hval, add_sub_cancel_right]
    · rw [hRneg]; exact ha

end S_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_edgeRegion_subset_affinoid_and_exists_mem_edgeRegion (solution)
