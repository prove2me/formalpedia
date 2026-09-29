-- Prove2me | solution 1 for CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/44dd4433-d240-576e-9a61-cfb632a0cd2e

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "gl_smul_def scalar_eq_scalarGL BruhatTits.gl_smul_def BruhatTits.scalar_eq_scalarGL"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane mem_affinoid_iff' gl_smul_def moebius pmoebius pmoebius_mk upperHalfPlane moebius_denom_ne_zero_of_mem"
namespace StabOmega0
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_linear_eq_max (ϖ : PseudoUniformizer K₀ K) {z : K} (hz : z ∈ affinoid ϖ 0) (α β : K₀) :
    Valued.v (algebraMap K₀ K α * z + algebraMap K₀ K β) =
      max (Valued.v (algebraMap K₀ K α)) (Valued.v (algebraMap K₀ K β)) := by
  rw [mem_affinoid_iff'] at hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [pow_zero] at hz1 hz2
  by_cases hα : α = 0
  · rw [hα, map_zero, zero_mul, zero_add, Valuation.map_zero, max_eq_right zero_le']
  have hα' : algebraMap K₀ K α ≠ 0 := (map_ne_zero _).mpr hα

  have hfac : algebraMap K₀ K α * z + algebraMap K₀ K β =
      algebraMap K₀ K α * (z - algebraMap K₀ K (-β / α)) := by
    rw [map_div₀, map_neg]
    field_simp
    ring
  have hβ : Valued.v (algebraMap K₀ K β) =
      Valued.v (algebraMap K₀ K α) * Valued.v (algebraMap K₀ K (-β / α)) := by
    rw [← Valuation.map_mul, ← map_mul, show α * (-β / α) = -β by field_simp, map_neg, Valuation.map_neg]
  have hkey : Valued.v (z - algebraMap K₀ K (-β / α)) = max 1 (Valued.v (algebraMap K₀ K (-β / α))) := by
    have hge := hz2 (-β / α)
    rcases le_or_gt (Valued.v (algebraMap K₀ K (-β / α))) 1 with ha | ha
    · rw [max_eq_left ha]
      apply le_antisymm _ hge
      calc Valued.v (z - algebraMap K₀ K (-β / α)) ≤ max (Valued.v z) (Valued.v (algebraMap K₀ K (-β / α))) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le hz1 ha
    · rw [max_eq_right ha.le]
      have hlt : Valued.v z < Valued.v (algebraMap K₀ K (-β / α)) := hz1.trans_lt ha
      exact Valuation.map_sub_eq_of_lt_right _ hlt
  rw [hfac, Valuation.map_mul, hβ, hkey, ← max_mul_mul_left, mul_one]

section Integral

variable {R : Type} [CommRing R] [Algebra R K₀]

theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

theorem one_le_max_of_one_le_v (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    {x y : K₀} {p q : R}
    (h : 1 ≤ Valued.v (algebraMap K₀ K (x * algebraMap R K₀ p - y * algebraMap R K₀ q))) :
    1 ≤ max (Valued.v (algebraMap K₀ K x)) (Valued.v (algebraMap K₀ K y)) := by
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  apply absurd h
  rw [not_le, map_sub, map_mul, map_mul]
  calc Valued.v (algebraMap K₀ K x * algebraMap K₀ K (algebraMap R K₀ p) -
          algebraMap K₀ K y * algebraMap K₀ K (algebraMap R K₀ q))
      ≤ max (Valued.v (algebraMap K₀ K x * algebraMap K₀ K (algebraMap R K₀ p)))
          (Valued.v (algebraMap K₀ K y * algebraMap K₀ K (algebraMap R K₀ q))) := Valuation.map_sub _ _ _
    _ = max (Valued.v (algebraMap K₀ K x) * Valued.v (algebraMap K₀ K (algebraMap R K₀ p)))
          (Valued.v (algebraMap K₀ K y) * Valued.v (algebraMap K₀ K (algebraMap R K₀ q))) := by
        rw [Valuation.map_mul, Valuation.map_mul]
    _ ≤ max (Valued.v (algebraMap K₀ K x) * 1) (Valued.v (algebraMap K₀ K y) * 1) :=
        max_le_max (mul_le_mul_right (hint p) _) (mul_le_mul_right (hint q) _)
    _ < 1 := by rw [mul_one, mul_one]; exact max_lt hlt.1 hlt.2

theorem moebius_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (a b c d : R) (hdet : IsUnit (a * d - b * c)) {w : K} (hw : w ∈ affinoid ϖ₁ 0) :
    (algebraMap K₀ K (algebraMap R K₀ a) * w + algebraMap K₀ K (algebraMap R K₀ b)) /
      (algebraMap K₀ K (algebraMap R K₀ c) * w + algebraMap K₀ K (algebraMap R K₀ d)) ∈ affinoid ϖ₁ 0 := by
  obtain ⟨u, hu⟩ := hdet
  have hdet1 : Valued.v (algebraMap K₀ K (algebraMap R K₀ (a * d - b * c))) = 1 := by
    rw [← hu]; exact v_algebraMap_units_eq_one hint u
  have hN : Valued.v (algebraMap K₀ K (algebraMap R K₀ a) * w + algebraMap K₀ K (algebraMap R K₀ b)) = 1 := by
    rw [v_linear_eq_max ϖ₁ hw]
    apply le_antisymm (max_le (hint a) (hint b))
    apply one_le_max_of_one_le_v hint (p := d) (q := c)
    rw [← map_mul, ← map_mul, ← map_sub, hdet1]
  have hD : Valued.v (algebraMap K₀ K (algebraMap R K₀ c) * w + algebraMap K₀ K (algebraMap R K₀ d)) = 1 := by
    rw [v_linear_eq_max ϖ₁ hw]
    apply le_antisymm (max_le (hint c) (hint d))
    apply one_le_max_of_one_le_v hint (p := b) (q := a)
    rw [← map_mul, ← map_mul, ← map_sub, show c * b - d * a = -(a * d - b * c) by ring, map_neg, map_neg,
      Valuation.map_neg, hdet1]
  have hD0 : algebraMap K₀ K (algebraMap R K₀ c) * w + algebraMap K₀ K (algebraMap R K₀ d) ≠ 0 :=
    (Valuation.ne_zero_iff _).mp (by rw [hD]; exact one_ne_zero)
  rw [mem_affinoid_iff']
  refine ⟨?_, fun t => ?_⟩
  · rw [pow_zero, Valuation.map_div, hN, hD, div_one]
  · rw [pow_zero, div_sub' hD0, Valuation.map_div, hD, div_one]
    have hrw : algebraMap K₀ K (algebraMap R K₀ a) * w + algebraMap K₀ K (algebraMap R K₀ b) -
        (algebraMap K₀ K (algebraMap R K₀ c) * w + algebraMap K₀ K (algebraMap R K₀ d)) * algebraMap K₀ K t =
        algebraMap K₀ K (algebraMap R K₀ a - t * algebraMap R K₀ c) * w +
          algebraMap K₀ K (algebraMap R K₀ b - t * algebraMap R K₀ d) := by
      rw [map_sub, map_sub, map_mul, map_mul]; ring
    rw [hrw, v_linear_eq_max ϖ₁ hw]
    apply one_le_max_of_one_le_v hint (p := d) (q := c)
    rw [show (algebraMap R K₀ a - t * algebraMap R K₀ c) * algebraMap R K₀ d -
        (algebraMap R K₀ b - t * algebraMap R K₀ d) * algebraMap R K₀ c = algebraMap R K₀ (a * d - b * c) by
      rw [map_sub, map_mul, map_mul]; ring, hdet1]

end Integral

end CerednikDrinfeld.Omega.StabOmega0

open CerednikDrinfeld.Omega.StabOmega0 in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    (h : GL (Fin 2) K₀) (hh : h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    {w : K} (hw : w ∈ affinoid ϖ₁ 0) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk h) w ∈ affinoid ϖ₁ 0 := by

  rw [CerednikDrinfeld.BruhatTits.gl_smul_def, LT.LatticeTree.Vertex.act_stdVertex_eq_iff] at hh
  obtain ⟨c, M, hM⟩ := hh

  have hmk : Matrix.ProjGenLinGroup.mk h =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap R K₀) M) := by
    rw [hM, map_mul, ← CerednikDrinfeld.BruhatTits.scalar_eq_scalarGL, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  have hwΩ : w ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hw
  rw [hmk, pmoebius_mk K₀ _ w (moebius_denom_ne_zero_of_mem K₀ hwΩ _), moebius]
  simp only [Matrix.GeneralLinearGroup.map_apply]
  have hdet : IsUnit (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
    rw [← Matrix.det_fin_two]
    exact Matrix.isUnits_det_units M
  exact moebius_mem_affinoid_zero ϖ₁ hint (M 0 0) (M 0 1) (M 1 0) (M 1 1) hdet hw

end S_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq (solution)
