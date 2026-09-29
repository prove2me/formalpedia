-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1d68f5dd-9fa8-5cda-b55f-e735a2479e11

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Theorems.Thm_CerednikDrinfeld_Omega_vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_residueSystem_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine.CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine.CerednikDrinfeld.Omega"

noncomputable section
open Classical

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine Omega.exists_finset_residueSystem_of_finite_quotient"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "vertexTube edgeTube PseudoUniformizer moebius pmoebius pmoebius_mk vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine exists_finset_residueSystem_of_finite_quotient"
namespace TubeShape
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_sub_comm (a b : K) : Valued.v (a - b) = Valued.v (b - a) := by
  rw [← Valuation.map_neg, neg_sub]

theorem v_sub_eq_of_lt_left {z c h : K} (hlt : Valued.v (c - h) < Valued.v (z - c)) : Valued.v (z - h) = Valued.v (z - c) := by
  have : z - h = (z - c) + (c - h) := by ring
  rw [this]; exact Valuation.map_add_eq_of_lt_left _ hlt

theorem v_sub_eq_of_lt_right {z c h : K} (hlt : Valued.v (z - c) < Valued.v (c - h)) : Valued.v (z - h) = Valued.v (c - h) := by
  have : z - h = (z - c) + (c - h) := by ring
  rw [this]; exact Valuation.map_add_eq_of_lt_right _ hlt

end CerednikDrinfeld.Omega.TubeShape

open CerednikDrinfeld.Omega.TubeShape in
theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) :
    (∃ (H : Finset C) (ρ : C → C), (∀ h ∈ H, ρ h ≠ 0) ∧
      ∀ z : C, z ∈ (vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) ∪
          vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ))) ↔
        Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ∧
          ∀ h ∈ H, Valued.v (ρ h) ≤ Valued.v (z - h)) ∧
    (∀ z : C, pmoebius K₀ (Matrix.ProjGenLinGroup.mk g)⁻¹ z =
      (z - algebraMap K₀ C c) / algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := by
  classical
  have hϖ0 : ϖ.ϖ ≠ 0 := edgeFlip_ne_zero K₀ ϖ
  have hpow : ϖ.ϖ ^ m = ϖ.ϖ ^ (m - 1) * ϖ.ϖ := by
    rw [zpow_sub_one₀ hϖ0, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]
  have hp₂eq : algebraMap K₀ C (ϖ.ϖ ^ m) = algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C ϖ.ϖ := by rw [hpow, map_mul]
  have hvϖ : Valued.v (algebraMap K₀ C ϖ.ϖ) < 1 := ϖ.lt_one
  have hp₁0 : algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) ≠ 0 := by rw [map_ne_zero]; exact zpow_ne_zero _ hϖ0
  have hp₂0 : algebraMap K₀ C (ϖ.ϖ ^ m) ≠ 0 := by rw [map_ne_zero]; exact zpow_ne_zero _ hϖ0
  have hvp₁0 : 0 < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := (Valuation.pos_iff _).2 hp₁0
  have hvp₂0 : 0 < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) := (Valuation.pos_iff _).2 hp₂0
  have hv21 : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := by
    rw [hp₂eq, map_mul]
    calc Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) * Valued.v (algebraMap K₀ C ϖ.ϖ) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) * 1 := mul_lt_mul_of_pos_left hvϖ hvp₁0
      _ = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := mul_one _

  obtain ⟨T, hT1, hTcov, -⟩ :=
    CerednikDrinfeld.Omega.exists_finset_residueSystem_of_finite_quotient R K₀ ϖ₀ hϖ₀ C hint hv
  obtain ⟨hV1, hE, hV2⟩ := CerednikDrinfeld.Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine R K₀ C ϖ ϖ₀ hϖ₀ hϖ hint hv c m g hg

  have hcoord : ∀ (p : K₀) (a : K₀), p ≠ 0 →
      algebraMap K₀ C a - algebraMap K₀ C c = algebraMap K₀ C p * algebraMap K₀ C ((a - c) * p⁻¹) := by
    intro p a hp
    rw [← map_mul, ← map_sub]; congr 1; field_simp
  refine ⟨?_, ?_⟩
  ·
    refine ⟨(T.filter fun t => Valued.v (algebraMap K₀ C t) = 1).image (fun t => algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C t) ∪
        T.image (fun t => algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t),
      fun h => if Valued.v (h - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) then algebraMap K₀ C (ϖ.ϖ ^ m) else algebraMap K₀ C (ϖ.ϖ ^ (m - 1)), ?_, ?_⟩
    · intro h _
      show (if Valued.v (h - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) then algebraMap K₀ C (ϖ.ϖ ^ m) else algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≠ 0
      split_ifs
      · exact hp₂0
      · exact hp₁0
    intro z
    have hnear : ∀ t : K₀, Valued.v (algebraMap K₀ C t) = 1 →
        (if Valued.v (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C t - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) then algebraMap K₀ C (ϖ.ϖ ^ m) else algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) = algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) := by
      intro t ht1
      rw [if_neg]
      rw [add_sub_cancel_left, map_mul, ht1, mul_one, not_le]; exact hv21
    have hfar : ∀ t ∈ T, (if Valued.v (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) then algebraMap K₀ C (ϖ.ϖ ^ m) else algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) = algebraMap K₀ C (ϖ.ϖ ^ m) := by
      intro t ht
      rw [if_pos]
      rw [add_sub_cancel_left, map_mul]
      calc Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * Valued.v (algebraMap K₀ C t) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * 1 := mul_le_mul_right (hT1 t ht) _
        _ = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) := mul_one _
    have hcnear : ∀ t : K₀, Valued.v (algebraMap K₀ C t) = 1 → Valued.v (algebraMap K₀ C c - (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C t)) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := by
      intro t ht1; rw [v_sub_comm, add_sub_cancel_left, map_mul, ht1, mul_one]
    have hcfar : ∀ t ∈ T, Valued.v (algebraMap K₀ C c - (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) := by
      intro t ht; rw [v_sub_comm, add_sub_cancel_left, map_mul]
      calc Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * Valued.v (algebraMap K₀ C t) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * 1 := mul_le_mul_right (hT1 t ht) _
        _ = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) := mul_one _
    rw [hV1, hE, hV2]
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    constructor
    ·
      intro hz
      have h0 : Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := by
        rcases hz with (⟨h, -⟩ | ⟨-, h⟩) | ⟨h, -⟩
        · exact h
        · exact h.le
        · exact h.trans hv21.le
      refine ⟨h0, ?_⟩
      rintro h (⟨t, ⟨ht, ht1⟩, rfl⟩ | ⟨t, ht, rfl⟩)
      ·
        rw [hnear t ht1]
        rcases hz with (⟨-, hall⟩ | ⟨-, h2⟩) | ⟨h1, -⟩
        · have := hall (c + ϖ.ϖ ^ (m - 1) * t)
          rwa [map_add, map_mul] at this
        · rw [v_sub_eq_of_lt_right (by rw [hcnear t ht1]; exact h2), hcnear t ht1]
        · rw [v_sub_eq_of_lt_right (by rw [hcnear t ht1]; exact lt_of_le_of_lt h1 hv21), hcnear t ht1]
      ·
        rw [hfar t ht]
        rcases hz with (⟨-, hall⟩ | ⟨h2, -⟩) | ⟨-, hall⟩
        · have hc := hall c
          have hlt : Valued.v (algebraMap K₀ C c - (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t)) < Valued.v (z - algebraMap K₀ C c) :=
            lt_of_le_of_lt (hcfar t ht) (lt_of_lt_of_le hv21 hc)
          rw [v_sub_eq_of_lt_left hlt]; exact (lt_of_lt_of_le hv21 hc).le
        · rw [v_sub_eq_of_lt_left (lt_of_le_of_lt (hcfar t ht) h2)]; exact h2.le
        · have := hall (c + ϖ.ϖ ^ m * t)
          rwa [map_add, map_mul] at this
    ·
      rintro ⟨h0, hH⟩
      by_cases h2 : Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m))
      ·
        refine Or.inr ⟨h2, fun a => ?_⟩
        by_cases ha : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) < Valued.v (algebraMap K₀ C a - algebraMap K₀ C c)
        · rw [v_sub_eq_of_lt_right (by rw [v_sub_comm (algebraMap K₀ C c)]; exact lt_of_le_of_lt h2 ha), v_sub_comm]; exact ha.le
        · push Not at ha
          set u : K₀ := (a - c) * (ϖ.ϖ ^ m)⁻¹ with hu
          have hau : algebraMap K₀ C a - algebraMap K₀ C c = algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C u := hcoord _ a (zpow_ne_zero _ hϖ0)
          have hu1 : Valued.v (algebraMap K₀ C u) ≤ 1 := by
            have : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * Valued.v (algebraMap K₀ C u) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * 1 := by
              rw [mul_one, ← map_mul, ← hau]; exact ha
            exact le_of_mul_le_mul_left this hvp₂0
          obtain ⟨t, ht, hut⟩ := hTcov u hu1
          have hρ := hH _ (Or.inr ⟨t, ht, rfl⟩)
          rw [hfar t ht] at hρ
          have hdist : Valued.v ((algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t) - algebraMap K₀ C a) < Valued.v (z - (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t)) := by
            have : (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ m) * algebraMap K₀ C t) - algebraMap K₀ C a = -(algebraMap K₀ C (ϖ.ϖ ^ m) * (algebraMap K₀ C u - algebraMap K₀ C t)) := by
              rw [mul_sub, ← hau]; ring
            rw [this, Valuation.map_neg, map_mul]
            calc Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * Valued.v (algebraMap K₀ C u - algebraMap K₀ C t) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) * 1 := mul_lt_mul_of_pos_left hut hvp₂0
              _ = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ m)) := mul_one _
              _ ≤ _ := hρ
          rw [v_sub_eq_of_lt_left hdist]; exact hρ
      · push Not at h2
        by_cases h1 : Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))
        · exact Or.inl (Or.inr ⟨h2, h1⟩)
        ·
          have hz1 : Valued.v (z - algebraMap K₀ C c) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := le_antisymm h0 (not_lt.1 h1)
          refine Or.inl (Or.inl ⟨h0, fun a => ?_⟩)
          rcases lt_trichotomy (Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))) (Valued.v (algebraMap K₀ C a - algebraMap K₀ C c)) with ha | ha | ha
          · rw [v_sub_eq_of_lt_right (by rw [v_sub_comm (algebraMap K₀ C c), hz1]; exact ha), v_sub_comm]; exact ha.le
          · set u : K₀ := (a - c) * (ϖ.ϖ ^ (m - 1))⁻¹ with hu
            have hau : algebraMap K₀ C a - algebraMap K₀ C c = algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C u := hcoord _ a (zpow_ne_zero _ hϖ0)
            have hu1 : Valued.v (algebraMap K₀ C u) = 1 := by
              have : Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) * Valued.v (algebraMap K₀ C u) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) * 1 := by
                rw [mul_one, ← map_mul, ← hau]; exact ha.symm
              exact mul_left_cancel₀ hvp₁0.ne' this
            obtain ⟨t, ht, hut⟩ := hTcov u hu1.le
            have ht1 : Valued.v (algebraMap K₀ C t) = 1 := by
              have : algebraMap K₀ C t = algebraMap K₀ C u + (algebraMap K₀ C t - algebraMap K₀ C u) := by ring
              rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [v_sub_comm, hu1]; exact hut), hu1]
            have hρ := hH _ (Or.inl ⟨t, ⟨ht, ht1⟩, rfl⟩)
            rw [hnear t ht1] at hρ
            have hdist : Valued.v ((algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C t) - algebraMap K₀ C a) < Valued.v (z - (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C t)) := by
              have : (algebraMap K₀ C c + algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * algebraMap K₀ C t) - algebraMap K₀ C a = -(algebraMap K₀ C (ϖ.ϖ ^ (m - 1)) * (algebraMap K₀ C u - algebraMap K₀ C t)) := by
                rw [mul_sub, ← hau]; ring
              rw [this, Valuation.map_neg, map_mul]
              calc Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) * Valued.v (algebraMap K₀ C u - algebraMap K₀ C t) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) * 1 := mul_lt_mul_of_pos_left hut hvp₁0
                _ = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) := mul_one _
                _ ≤ _ := hρ
            rw [v_sub_eq_of_lt_left hdist]; exact hρ
          · rw [v_sub_eq_of_lt_left (by rw [v_sub_comm (algebraMap K₀ C c), hz1]; exact ha), hz1]
  ·
    intro z
    have hinv : (Matrix.ProjGenLinGroup.mk g)⁻¹ = Matrix.ProjGenLinGroup.mk g⁻¹ := (map_inv Matrix.ProjGenLinGroup.mk g).symm
    set gi : Matrix (Fin 2) (Fin 2) K₀ := !![(ϖ.ϖ ^ (m - 1))⁻¹, -(c * (ϖ.ϖ ^ (m - 1))⁻¹); 0, 1] with hgi
    have hpm : ϖ.ϖ ^ (m - 1) ≠ 0 := zpow_ne_zero _ hϖ0
    have hmul : (g : Matrix (Fin 2) (Fin 2) K₀) * gi = 1 := by
      rw [hg, hgi]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hpm] <;> (try field_simp) <;> (try ring)
    have hginv : ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = gi := by
      rw [Matrix.coe_units_inv]; exact Matrix.inv_eq_right_inv hmul
    have e10 : (g⁻¹ : GL (Fin 2) K₀) 1 0 = 0 := by
      show ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0
      rw [hginv, hgi]; simp
    have e11 : (g⁻¹ : GL (Fin 2) K₀) 1 1 = 1 := by
      show ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1
      rw [hginv, hgi]; simp
    have e00 : (g⁻¹ : GL (Fin 2) K₀) 0 0 = (ϖ.ϖ ^ (m - 1))⁻¹ := by
      show ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) 0 0 = _
      rw [hginv, hgi]; simp
    have e01 : (g⁻¹ : GL (Fin 2) K₀) 0 1 = -(c * (ϖ.ϖ ^ (m - 1))⁻¹) := by
      show ((g⁻¹ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) 0 1 = _
      rw [hginv, hgi]; simp
    have hden : algebraMap K₀ C ((g⁻¹ : GL (Fin 2) K₀) 1 0) * z + algebraMap K₀ C ((g⁻¹ : GL (Fin 2) K₀) 1 1) ≠ 0 := by
      rw [e10, e11, map_zero, zero_mul, zero_add, map_one]; exact one_ne_zero
    rw [hinv, pmoebius_mk K₀ g⁻¹ z hden, moebius, e10, e11, e00, e01, map_zero, zero_mul, zero_add, map_one, div_one,
      map_neg, map_mul, map_inv₀, eq_div_iff hp₁0]
    field_simp
    ring

end

end S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine (solution)
