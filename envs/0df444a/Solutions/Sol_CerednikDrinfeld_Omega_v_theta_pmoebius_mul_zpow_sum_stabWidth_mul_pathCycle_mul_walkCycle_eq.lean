-- Prove2me | solution 1 for CerednikDrinfeld.Omega.v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/603a1381-c3d0-5e48-a931-afbd4810c260

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
import Theorems.Thm_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_Omega_v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle
import Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_basePoint
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_smul_stdVertex_eq_of_mem_affinoid_zero
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer

import Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_eq_theta
import Mathlib

import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford"

noncomputable section

namespace Cur

section Kit

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_apply_eq_of_isUnit [IsAlgClosed K] (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q))
    (hF : IsUnit F) {w w' : K} (hw : w ∈ affinoid Q 0) (hw' : w' ∈ affinoid Q 0) :
    Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane Q 0 hw⟩) =
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane Q 0 hw'⟩) := by
  obtain ⟨G, hFG⟩ := hF.exists_right_inv
  have hprod : restrictAffinoid Q 0 (F : ↥(upperHalfPlane K₀ K) → K) *
      restrictAffinoid Q 0 (G : ↥(upperHalfPlane K₀ K) → K) = 1 := by
    funext z
    have := congrArg (fun H : ↥(holRing Q) => (H : ↥(upperHalfPlane K₀ K) → K)
      (Set.inclusion (affinoid_subset_upperHalfPlane Q 0) z)) hFG
    simp at this
    exact this
  exact v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one Q ((mem_holRing_iff Q _).1 F.2 0)
    ((mem_holRing_iff Q _).1 G.2 0) hprod ⟨w, hw⟩ ⟨w', hw'⟩

def translate (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q)) (g : PGL(2, K₀)) : ↥(holRing Q) := g⁻¹ • F

theorem translate_apply (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q)) (g : PGL(2, K₀))
    (z : ↥(upperHalfPlane K₀ K)) :
    (translate Q F g : ↥(upperHalfPlane K₀ K) → K) z = (F : ↥(upperHalfPlane K₀ K) → K) (g • z) := by
  rw [translate, coe_smul_holRing_apply, inv_inv]

theorem isUnit_translate (Q : PseudoUniformizer K₀ K) {F : ↥(holRing Q)} (hF : IsUnit F) (g : PGL(2, K₀)) :
    IsUnit (translate Q F g) :=
  hF.map (MulSemiringAction.toRingHom _ ↥(holRing Q) g⁻¹)

end Kit

theorem exists_potential
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ (Φ : LT.LatticeTree.Vertex R K₀ → Γ₀) (μ : LT.LatticeTree.Vertex R K₀ → LT.LatticeTree.Vertex R K₀ → ℤ),
      (∀ x, Φ x ≠ 0) ∧
      (∀ (g : GL (Fin 2) K₀) (w : K) (hw : w ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
          (Matrix.ProjGenLinGroup.mk g • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Φ (g • LT.LatticeTree.stdVertex R K₀)) ∧
      (∀ x y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj x y →
        Φ y = Φ x * Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ μ x y) ∧
      (∀ x y : LT.LatticeTree.Vertex R K₀, μ y x = -μ x y) ∧
      (∀ (x : LT.LatticeTree.Vertex R K₀) (S : Finset (LT.LatticeTree.Vertex R K₀)),
        (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj x y) → ∑ y ∈ S, μ x y = 0) := by
  classical
  set v₀ : LT.LatticeTree.Vertex R K₀ := LT.LatticeTree.stdVertex R K₀ with hv₀
  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hqdef
  have hq0 : 0 < q := by rw [hqdef, ← hϖ₁]; exact ϖ₁.pos
  have hq1 : q < 1 := by rw [hqdef, ← hϖ₁]; exact ϖ₁.lt_one
  have hqinj : Function.Injective (fun k : ℤ => q ^ k) := zpow_right_injective₀ hq0 hq1.ne

  have hFne : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) z) ≠ 0 := by
    intro z h0
    obtain ⟨G, hFG⟩ := hF.exists_right_inv
    have := congrArg (fun H : ↥(holRing ϖ₁) => (H : ↥(upperHalfPlane K₀ K) → K) z) hFG
    rw [show ((F * G : ↥(holRing ϖ₁)) : ↥(upperHalfPlane K₀ K) → K) z =
      (F : ↥(upperHalfPlane K₀ K) → K) z * (G : ↥(upperHalfPlane K₀ K) → K) z from rfl,
      (Valuation.zero_iff _).1 h0, zero_mul] at this
    exact zero_ne_one this

  have hW : ∀ (g g' : GL (Fin 2) K₀), g • v₀ = g' • v₀ →
      ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk g') • ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩)) := by
    intro g g' hgg' w w' hw hw'
    set h : GL (Fin 2) K₀ := g⁻¹ * g' with hh
    have hhv : h • v₀ = v₀ := by rw [hh, mul_smul, ← hgg', inv_smul_smul]
    have hD := pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq R K₀ K hint hv ϖ₁ h hhv hw'
    have hg' : Matrix.ProjGenLinGroup.mk g' = Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk h := by
      rw [← map_mul, hh, mul_inv_cancel_left]
    have hpt : (Matrix.ProjGenLinGroup.mk g') • (⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩ : ↥(upperHalfPlane K₀ K)) =
        (Matrix.ProjGenLinGroup.mk g) •
          ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk h) w', affinoid_subset_upperHalfPlane ϖ₁ 0 hD⟩ := by
      rw [hg', mul_smul]
      rfl
    rw [hpt, ← translate_apply ϖ₁ F, ← translate_apply ϖ₁ F]
    exact v_apply_eq_of_isUnit ϖ₁ (translate ϖ₁ F _) (isUnit_translate ϖ₁ hF _) hw hD

  have hchart : ∀ x : LT.LatticeTree.Vertex R K₀, ∃ g : GL (Fin 2) K₀, g • v₀ = x :=
    fun x => LT.LatticeTree.exists_act_stdVertex_eq R K₀ x
  choose gsel hgsel using hchart
  have hback : ∀ x : LT.LatticeTree.Vertex R K₀, (gsel x)⁻¹ • x = v₀ :=
    fun x => inv_smul_eq_iff.mpr (hgsel x).symm

  have hA : ∀ g : GL (Fin 2) K₀, ∃ m : LT.LatticeTree.Vertex R K₀ → ℤ,
      (∀ S : Finset (LT.LatticeTree.Vertex R K₀),
        (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj v₀ y) → ∑ y ∈ S, m y = 0) ∧
      ∀ y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj v₀ y →
        ∀ (g' : GL (Fin 2) K₀), g' • LT.LatticeTree.stdVertex R K₀ = y →
          ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
            Valued.v ((translate ϖ₁ F (Matrix.ProjGenLinGroup.mk g) : ↥(upperHalfPlane K₀ K) → K)
                ((Matrix.ProjGenLinGroup.mk g') • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
              Valued.v ((translate ϖ₁ F (Matrix.ProjGenLinGroup.mk g) : ↥(upperHalfPlane K₀ K) → K)
                  ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
                Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (m y) := fun g =>
    exists_int_neighbours_sum_eq_zero_v_apply_smul_eq R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hϖ₁
      (translate ϖ₁ F (Matrix.ProjGenLinGroup.mk g)) (isUnit_translate ϖ₁ hF _)
  choose m hmsum hmraw using hA

  by_cases hne : ∃ w₀ : K, w₀ ∈ affinoid ϖ₁ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ => 0, fun _ => one_ne_zero, ?_, ?_, ?_, ?_⟩
    · intro g w hw; exact (hne ⟨w, hw⟩).elim
    · intro x y _; rw [zpow_zero, mul_one]
    · intro x y; rw [neg_zero]
    · intro x S _; exact Finset.sum_const_zero
  obtain ⟨w₀, hw₀⟩ := hne

  set Φ : LT.LatticeTree.Vertex R K₀ → Γ₀ := fun x =>
    Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
      ((Matrix.ProjGenLinGroup.mk (gsel x)) • ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩)) with hΦ
  have hΦg : ∀ (x : LT.LatticeTree.Vertex R K₀) (g : GL (Fin 2) K₀), g • v₀ = x →
      ∀ (w : K) (hw : w ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) = Φ x :=
    fun x g hg w hw => hW g (gsel x) (by rw [hg, hgsel]) w w₀ hw hw₀
  have hΦ0 : ∀ x, Φ x ≠ 0 := fun x => hFne _

  have hmstep : ∀ (g : GL (Fin 2) K₀) (y : LT.LatticeTree.Vertex R K₀), (BruhatTits.tree R K₀).Adj v₀ y →
      Φ (g • y) = Φ (g • v₀) * q ^ (m g y) := by
    intro g y hy
    have h := hmraw g y hy (gsel y) (hgsel y) w₀ w₀ hw₀ hw₀
    rw [translate_apply, translate_apply, ← mul_smul, ← map_mul] at h
    rw [← hΦg (g • y) (g * gsel y) (by rw [mul_smul, hgsel]) w₀ hw₀, ← hΦg (g • v₀) g rfl w₀ hw₀]
    exact h
  set μ : LT.LatticeTree.Vertex R K₀ → LT.LatticeTree.Vertex R K₀ → ℤ := fun x y =>
    if (BruhatTits.tree R K₀).Adj x y then m (gsel x) ((gsel x)⁻¹ • y) else 0 with hμ

  have hjump : ∀ x y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj x y → Φ y = Φ x * q ^ μ x y := by
    intro x y hxy
    have hy : (BruhatTits.tree R K₀).Adj v₀ ((gsel x)⁻¹ • y) := by
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel x)⁻¹ hxy
      rwa [hback x] at this
    have := hmstep (gsel x) _ hy
    rw [smul_inv_smul, hgsel] at this
    rw [this, hμ]
    simp only [if_pos hxy]
  refine ⟨Φ, μ, hΦ0, fun g w hw => hΦg _ g rfl w hw, hjump, ?_, ?_⟩
  ·
    intro x y
    by_cases hxy : (BruhatTits.tree R K₀).Adj x y
    · have h1 := hjump x y hxy
      have h2 := hjump y x hxy.symm
      rw [h1, mul_assoc, ← zpow_add₀ hq0.ne'] at h2
      have h3 : Φ x * q ^ (0 : ℤ) = Φ x * q ^ (μ x y + μ y x) := by rw [zpow_zero, mul_one]; exact h2
      have := hqinj (mul_left_cancel₀ (hΦ0 x) h3)
      omega
    · have hyx : ¬ (BruhatTits.tree R K₀).Adj y x := fun h => hxy h.symm
      simp only [hμ, if_neg hxy, if_neg hyx, neg_zero]
  ·
    intro x S hS
    have hS' : ∀ y ∈ S, μ x y = m (gsel x) ((gsel x)⁻¹ • y) := fun y hy => by
      simp only [hμ, if_pos ((hS y).1 hy)]
    rw [Finset.sum_congr rfl hS']
    rw [← Finset.sum_image (f := fun y => m (gsel x) y) (g := fun y => (gsel x)⁻¹ • y)
      (fun a _ b _ h => smul_left_cancel _ h)]
    refine hmsum (gsel x) _ (fun y => ?_)
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel x)⁻¹ ((hS z).1 hz)
      rwa [hback x] at this
    · intro hy
      refine ⟨gsel x • y, (hS _).2 ?_, inv_smul_smul _ _⟩
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel x) hy
      rwa [hgsel x] at this

end Cur

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.ActsThrough Mumford.dartIndex Mumford.walkCycle Mumford.pathCycle Mumford.walkCycle_nil Mumford.walkCycle_cons Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert Mumford.stabWidth Mumford.GraphAction.smul_adj DegeneracyData degeneracyMatrix pushforward ribbonKernel mem_ribbonKernel gl_smul_def pgl_mk_smul tree BruhatTits.gl_smul_def BruhatTits.tree BruhatTits.pgl_mk_smul Omega.v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle Omega.theta_mul_theta_basePoint Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul Omega.isDiscrete_of_finite_stabilizer_stdVertex BruhatTits.tree_isTree Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle Omega.holRing_eq_and_affinoid_zero_eq BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane affinoid_mono mem_affinoid_iff' IsExhausted restrictAffinoid holRing mem_holRing_iff exists_mapsTo_affinoid coe_smul_holRing_apply gl_smul_def pmoebius upperHalfPlane pmoebius_mem_upperHalfPlane pmoebius_one pmoebius_mul crossRatio thetaFactor theta IsDiscrete exists_int_neighbours_sum_eq_zero_v_apply_smul_eq pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle theta_mul_theta_basePoint exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul isDiscrete_of_finite_stabilizer_stdVertex thetaMultipliable_of_isDiscrete_of_isExhausted smul_stdVertex_eq_of_mem_affinoid_zero holRing_eq_and_affinoid_zero_eq theta_mul_theta_eq_theta finite_setOf_pmoebius_mem_affinoid"
namespace GlobalCurrent
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

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

theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le'
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

theorem exists_pow_le_v_algebraMap_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))⁻¹ ^ N := by
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  refine ⟨k.natAbs, ?_, ?_⟩
  · rw [hk, ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (Int.le_natAbs)
  · rw [hk, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (by rw [Int.natCast_natAbs]; exact neg_abs_le k)

def treePseudoUniformizer (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    PseudoUniformizer K₀ K where
  ϖ := algebraMap R K₀ ϖ
  pos := v_algebraMap_pos hϖ
  lt_one := v_algebraMap_lt_one hϖ hv
  scale := exists_pow_le_v_algebraMap_le hϖ hint hv

@[scoped simp] theorem treePseudoUniformizer_ϖ (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    (treePseudoUniformizer hϖ hint hv).ϖ = algebraMap R K₀ ϖ := rfl

end PUTree

end CerednikDrinfeld.Omega.GlobalCurrent
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld"

namespace FTWcore

open Finset

section Kappa

variable {W : Type} (𝒯 : SimpleGraph W) (τ : W → ZMod 2)

theorem zmod2_eq_or_eq (a b c : ZMod 2) (h : a ≠ b) : a = c ∨ b = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

theorem eq_neg_of_two_step (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v) (c₀ : ZMod 2)
    (μ Wt : W → W → ℤ)
    (hμ : ∀ x y, 𝒯.Adj x y → μ y x = -μ x y) (hW : ∀ x y, 𝒯.Adj x y → Wt y x = -Wt x y)
    (htwo : ∀ v y y', τ v = c₀ → 𝒯.Adj v y → 𝒯.Adj v y' → μ y v + μ v y' = -(Wt y v + Wt v y'))
    (hK : ∀ v, τ v = c₀ → ∃ S : Finset W, (∀ y, y ∈ S ↔ 𝒯.Adj v y) ∧ S.Nonempty ∧
      ∑ y ∈ S, μ v y = 0 ∧ ∑ y ∈ S, Wt v y = 0) :
    ∀ x y, 𝒯.Adj x y → μ x y = -Wt x y := by

  have hout : ∀ v y, τ v = c₀ → 𝒯.Adj v y → μ v y + Wt v y = 0 := by
    intro v y hv hvy
    obtain ⟨S, hS, hne, hSμ, hSW⟩ := hK v hv

    have hconst : ∀ y' ∈ S, μ v y' + Wt v y' = μ v y + Wt v y := by
      intro y' hy'
      have h2 := htwo v y y' hv hvy ((hS y').1 hy')
      rw [hμ v y hvy, hW v y hvy] at h2
      linarith
    have hsum : ∑ y' ∈ S, (μ v y' + Wt v y') = S.card • (μ v y + Wt v y) := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const]
    rw [Finset.sum_add_distrib, hSμ, hSW, zero_add, nsmul_eq_mul] at hsum
    have hcard : (S.card : ℤ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hne)
    exact (mul_eq_zero.mp hsum.symm).resolve_left hcard
  intro x y hxy
  rcases zmod2_eq_or_eq (τ x) (τ y) c₀ (hadj x y hxy) with hx | hy
  · linarith [hout x y hx hxy]
  · have := hout y x hy hxy.symm
    rw [hμ x y hxy, hW x y hxy] at this
    linarith

end Kappa
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent"

section WalkSum

variable {W : Type} {𝒯 : SimpleGraph W} {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

def dartSum (μ : W → W → ℤ) {u v : W} (p : 𝒯.Walk u v) : ℤ := (p.darts.map fun d => μ d.fst d.snd).sum

@[scoped simp] theorem dartSum_nil (μ : W → W → ℤ) (u : W) : dartSum μ (SimpleGraph.Walk.nil : 𝒯.Walk u u) = 0 := by
  simp [dartSum]

@[scoped simp] theorem dartSum_cons (μ : W → W → ℤ) {u v w : W} (h : 𝒯.Adj u v) (p : 𝒯.Walk v w) :
    dartSum μ (SimpleGraph.Walk.cons h p) = μ u v + dartSum μ p := by
  simp [dartSum]

theorem potential_walk (Φ : W → Γ₀) (q : Γ₀) (hq : q ≠ 0) (μ : W → W → ℤ)
    (hjump : ∀ x y, 𝒯.Adj x y → Φ y = Φ x * q ^ μ x y) :
    ∀ {u v : W} (p : 𝒯.Walk u v), Φ v = Φ u * q ^ dartSum μ p := by
  intro u v p
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [dartSum_cons, zpow_add₀ hq, ← mul_assoc, ← hjump _ _ h, ih]

theorem dartSum_eq_neg (μ Wt : W → W → ℤ) (h : ∀ x y, 𝒯.Adj x y → μ x y = -Wt x y) :
    ∀ {u v : W} (p : 𝒯.Walk u v), dartSum μ p = -dartSum Wt p := by
  intro u v p
  induction p with
  | nil => simp
  | cons h' p ih => rw [dartSum_cons, dartSum_cons, ih, h _ _ h']; ring

theorem sum_mul_walkCycle_eq_dartSum {G : Type} [Group G] [MulAction G W] [Mumford.GraphAction G 𝒯]
    [DecidableEq (Mumford.QuotEdge G 𝒯)] [DecidableRel 𝒯.Adj] {E : Type} [Fintype E]
    (orb : E → Mumford.QuotEdge G 𝒯) (A : E → ℤ) :
    ∀ {u v : W} (p : 𝒯.Walk u v),
      ∑ e, A e * Mumford.walkCycle 𝒯 orb p e =
        dartSum (fun x y => if h : 𝒯.Adj x y then ∑ e, A e * Mumford.dartIndex 𝒯 (orb e) ⟨(x, y), h⟩ else 0) p := by
  intro u v p
  induction p with
  | nil => simp [Mumford.walkCycle_nil]
  | cons h p ih =>
    rw [dartSum_cons, dif_pos h, ← ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Mumford.walkCycle_cons, mul_add]

end WalkSum
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent"

end FTWcore
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section E3sec
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits LT.LatticeTree MulAction"

namespace FTW

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem quotEdge_eq_iff (d d' : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯) = Quotient.mk _ d' ↔ ∃ g : G, g • d' = d := by
  rw [Quotient.eq]; exact MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff

theorem quotVert_eq_iff (a b : W) :
    (Quotient.mk (orbitRel G W) a : QuotVert G W) = Quotient.mk _ b ↔ ∃ g : G, g • b = a := by
  rw [Quotient.eq]; exact MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff

theorem exists_smul_eq_out (d : 𝒯.Dart) :
    ∃ g : G, g • d = (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out := by
  have h := Quotient.out_eq (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯)
  exact (quotEdge_eq_iff _ _).1 h

theorem exists_smul_eq_out' (q : QuotEdge G 𝒯) (d : 𝒯.Dart) (h : Quotient.mk (orbitRel G 𝒯.Dart) d = q) :
    ∃ g : G, g • d = q.out := by
  subst h; exact exists_smul_eq_out d

section Colour

variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
include hτ hadj

theorem colour_snd_of_fst_eq_zero (d : 𝒯.Dart) (h : τ d.fst = 0) : τ d.snd = 1 := by
  rcases zmod2_cases (τ d.snd) with h1 | h1
  · exact absurd (h.trans h1.symm) (hadj _ _ d.adj)
  · exact h1

theorem colour_fst_of_ne_zero (d : 𝒯.Dart) (h : τ d.fst ≠ 0) : τ d.fst = 1 ∧ τ d.snd = 0 := by
  rcases zmod2_cases (τ d.fst) with h0 | h1
  · exact absurd h0 h
  · rcases zmod2_cases (τ d.snd) with h2 | h2
    · exact ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) (hadj _ _ d.adj)

theorem colour_out_fst (d : 𝒯.Dart) :
    τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = τ d.fst := by
  obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) d
  rw [← hg, smul_dart_fst, hτ]

end Colour
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section Kernel

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]

noncomputable def orientDatum (τ : W → ZMod 2) [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0}) : DegeneracyData E (QuotVert G W) :=
  ⟨fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.fst,
   fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.snd, fun _ => 1⟩

theorem pathCycle_mem_ribbonKernel (hT : 𝒯.IsTree)
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert G W)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0}) (v₀ : W) (α : G) :
    pathCycle 𝒯 (fun e => (eE e).1) v₀ α ∈
      CerednikDrinfeld.ribbonKernel
        (⟨fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.fst,
          fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.snd, fun _ => 1⟩ : DegeneracyData E (QuotVert G W)) := by
  obtain ⟨φ, hφ⟩ := CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle 𝒯 hT τ hτ hadj
    (⟨fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.fst,
      fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.snd, fun _ => 1⟩ : DegeneracyData E (QuotVert G W))
    eE (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) v₀
  rw [← hφ α]
  exact (φ _).2

end Kernel
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section Neighbours

variable (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]

theorem exists_neighbourFinset_stdVertex (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] :
    ∃ S : Finset (Vertex R K₀), ∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj (stdVertex R K₀) y := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective R K₀ (by rw [h, map_zero]))
  let n : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, algebraMap R K₀ ϖ]
    (by rw [Matrix.det_fin_two_of]; simpa using hϖ0)
  let s : R → GL (Fin 2) K₀ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero !![algebraMap R K₀ t, 1; 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp)
  obtain ⟨hadjn, hsfix, hnbrs, hcong, hne⟩ :=
    CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ n rfl s (fun t => rfl)
  refine ⟨insert (n • stdVertex R K₀) (Finset.univ.image fun x : R ⧸ Ideal.span {ϖ} => (s (Quotient.out x) * n) • stdVertex R K₀),
    fun y => ?_⟩
  rw [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | ⟨x, -, rfl⟩)
    · exact hadjn
    · have h := Mumford.GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (s (Quotient.out x)) hadjn
      rwa [hsfix, ← mul_smul] at h
  · intro hy
    rcases hnbrs y hy with h | ⟨t, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨Ideal.Quotient.mk (Ideal.span {ϖ}) t, Finset.mem_univ _, ?_⟩
      apply (hcong _ _).2
      have : t - Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) t) ∈ Ideal.span {ϖ} := by
        rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      rw [← Ideal.mem_span_singleton]
      rw [show Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) t) - t = -(t - Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) t)) by ring]
      exact (Ideal.span {ϖ}).neg_mem this

theorem exists_neighbourFinset (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (x : Vertex R K₀) :
    ∃ S : Finset (Vertex R K₀), ∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj x y := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_neighbourFinset_stdVertex R K₀ ϖ hϖ
  obtain ⟨g, hg⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ x
  rw [← CerednikDrinfeld.BruhatTits.gl_smul_def] at hg
  refine ⟨S₀.image fun y => g • y, fun y => ?_⟩
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y₀, hy₀, rfl⟩
    rw [← hg]
    exact Mumford.GraphAction.smul_adj g ((hS₀ y₀).1 hy₀)
  · intro hy
    refine ⟨g⁻¹ • y, (hS₀ _).2 ?_, smul_inv_smul g y⟩
    have h := Mumford.GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) g⁻¹ hy
    rwa [← hg, inv_smul_smul] at h

theorem exists_adj (ϖ : R) (hϖ : Irreducible ϖ) (x : Vertex R K₀) : ∃ y, (BruhatTits.tree R K₀).Adj x y := by
  classical
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective R K₀ (by rw [h, map_zero]))
  let n : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, algebraMap R K₀ ϖ]
    (by rw [Matrix.det_fin_two_of]; simpa using hϖ0)
  let s : R → GL (Fin 2) K₀ := fun t => Matrix.GeneralLinearGroup.mkOfDetNeZero !![algebraMap R K₀ t, 1; 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp)
  obtain ⟨hadjn, -, -, -, -⟩ :=
    CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ n rfl s (fun t => rfl)
  obtain ⟨g, hg⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ x
  rw [← CerednikDrinfeld.BruhatTits.gl_smul_def] at hg
  refine ⟨g • (n • stdVertex R K₀), ?_⟩
  rw [← hg]
  exact Mumford.GraphAction.smul_adj g hadjn

end Neighbours
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section OneDart

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
variable [DecidableEq (QuotEdge G 𝒯)] {E : Type} (orb : E → QuotEdge G 𝒯)

theorem walkCycle_cons_nil {x y : W} (h : 𝒯.Adj x y) (e : E) :
    walkCycle 𝒯 orb (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) e = dartIndex 𝒯 (orb e) ⟨(x, y), h⟩ := by
  rw [walkCycle_cons, walkCycle_nil, Pi.zero_apply, add_zero]

variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
variable [Fintype E] (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})

include hτ hadj in

theorem dartIndex_of_fst_eq_zero (d : 𝒯.Dart) (h0 : τ d.fst = 0) (e : E) :
    dartIndex 𝒯 (eE e).1 d = if Quotient.mk (orbitRel G 𝒯.Dart) d = (eE e).1 then 1 else 0 := by
  rw [dartIndex, sub_eq_self, if_neg]
  intro h
  have h1 : τ d.symm.fst = 0 := by rw [← colour_out_fst τ hτ hadj d.symm, h]; exact (eE e).2
  rw [SimpleGraph.Dart.symm_toProd] at h1
  have h2 := colour_snd_of_fst_eq_zero τ hτ hadj d h0
  exact absurd (h2.symm.trans h1) one_ne_zero

include hτ hadj in

theorem dartIndex_of_fst_ne_zero (d : 𝒯.Dart) (h1 : τ d.fst ≠ 0) (e : E) :
    dartIndex 𝒯 (eE e).1 d = -(if Quotient.mk (orbitRel G 𝒯.Dart) d.symm = (eE e).1 then 1 else 0) := by
  rw [dartIndex, if_neg, zero_sub]
  intro h
  apply h1
  rw [← colour_out_fst τ hτ hadj d, h]; exact (eE e).2

end OneDart
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section Star

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
variable (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))
variable (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
variable [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert G W)] {E : Type} [Fintype E]
variable (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})

omit hτ hadj in
include hfin in
theorem finite_stabilizer_dart' (d : 𝒯.Dart) : Finite (MulAction.stabilizer G d) := by
  haveI := hfin d.fst
  have hle : ∀ s : G, s ∈ MulAction.stabilizer G d → s ∈ MulAction.stabilizer G d.fst := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff] at hs ⊢
    rw [← smul_dart_fst, hs]
  exact Finite.of_injective (fun s : MulAction.stabilizer G d => (⟨s.1, hle s.1 s.2⟩ : MulAction.stabilizer G d.fst))
    (fun s t h => Subtype.ext (by have := congrArg (fun x : MulAction.stabilizer G d.fst => (x : G)) h; exact this))

omit hτ hadj in
include hfin in
theorem stabWidth_coe_eq' (d : 𝒯.Dart) (q : QuotEdge G 𝒯) (hq : Quotient.mk (orbitRel G 𝒯.Dart) d = q) :
    ((stabWidth G 𝒯 q : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G d) : ℤ) := by
  haveI := finite_stabilizer_dart' 𝒯 hfin d
  have h1 : stabWidth G 𝒯 q = Nat.toPNat' (Nat.card (MulAction.stabilizer G d)) := by
    rw [← hq]; exact stabWidth_mk 𝒯 d
  have h2 : ((Nat.toPNat' (Nat.card (MulAction.stabilizer G d)) : ℕ+) : ℕ) = Nat.card (MulAction.stabilizer G d) := by
    rw [Nat.toPNat'_coe, if_pos Nat.card_pos]
  rw [h1, h2]

theorem card_filter_smul_eq' {H : Subgroup G} [Fintype H] {X : Type} [MulAction G X] [DecidableEq X]
    (x : X) (h₀ : H) :
    (Finset.univ.filter fun h : H => (h : G) • x = (h₀ : G) • x).card = Fintype.card {s : H // (s : G) • x = x} := by
  classical
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun h => ⟨h₀⁻¹ * h.1, ?_⟩
      invFun := fun s => ⟨h₀ * s.1, ?_⟩
      left_inv := fun h => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  · show ((h₀⁻¹ * h.1 : H) : G) • x = x
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, h.2, inv_smul_smul]
  · show ((h₀ * s.1 : H) : G) • x = (h₀ : G) • x
    rw [Subgroup.coe_mul, mul_smul, s.2]

theorem pushforward_apply' {V : Type} [DecidableEq V] (f : E → V) (x : E → ℤ) (v : V) :
    pushforward f x v = ∑ e ∈ Finset.univ.filter (fun e => f e = v), x e := by
  simp only [pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

include hfin hτ hadj in

theorem sum_weight_dartIndex_eq_zero
    (c : E → ℤ)
    (hc : c ∈ CerednikDrinfeld.ribbonKernel
      (⟨fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.fst,
        fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.snd, fun _ => 1⟩ : DegeneracyData E (QuotVert G W)))
    (x : W) (S : Finset W) (hS : ∀ y, y ∈ S ↔ 𝒯.Adj x y) :
    ∑ y ∈ S.attach, ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e *
        dartIndex 𝒯 (eE e).1 ⟨(x, y.1), (hS y.1).1 y.2⟩ = 0 := by
  classical

  set F : W → ℤ := fun y => if h : 𝒯.Adj x y then
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e * dartIndex 𝒯 (eE e).1 ⟨(x, y), h⟩ else 0 with hF
  have hattach : ∑ y ∈ S.attach, ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e *
        dartIndex 𝒯 (eE e).1 ⟨(x, y.1), (hS y.1).1 y.2⟩ = ∑ y ∈ S, F y := by
    rw [← Finset.sum_attach S F]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hF, dif_pos ((hS y.1).1 y.2)]
  rw [hattach]
  haveI : Finite (MulAction.stabilizer G x) := hfin x
  haveI : Fintype (MulAction.stabilizer G x) := Fintype.ofFinite _
  set v : QuotVert G W := Quotient.mk (orbitRel G W) x with hv
  set Da : E → QuotVert G W := fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.fst with hDa
  set Db : E → QuotVert G W := fun e => Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.snd with hDb

  have hker : pushforward Da c = 0 ∧ pushforward Db c = 0 := by
    have h := (CerednikDrinfeld.mem_ribbonKernel).1 hc
    exact ⟨h 0, h 1⟩
  have hca : ∑ e ∈ Finset.univ.filter (fun e => Da e = v), c e = 0 := by
    rw [← pushforward_apply' Da c v, hker.1]; rfl
  have hcb : ∑ e ∈ Finset.univ.filter (fun e => Db e = v), c e = 0 := by
    rw [← pushforward_apply' Db c v, hker.2]; rfl
  rcases zmod2_cases (τ x) with hx0 | hx1
  ·
    have hex : ∀ e : E, Da e = v → ∃ g : G, g • (eE e).1.out.fst = x := by
      intro e he
      have he' : Quotient.mk (orbitRel G W) x = Quotient.mk (orbitRel G W) (eE e).1.out.fst := by
        rw [hv] at he; simp only [hDa] at he; exact he.symm
      exact (quotVert_eq_iff _ _).1 he'
    choose! gg hgg using hex
    obtain ⟨δ, hδfst, hδcls⟩ : ∃ δ : E → 𝒯.Dart, (∀ e, Da e = v → (δ e).fst = x) ∧
        (∀ e, Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = (eE e).1) := by
      refine ⟨fun e => gg e • (eE e).1.out, fun e he => ?_, fun e => ?_⟩
      · rw [smul_dart_fst, hgg e he]
      · rw [← Quotient.out_eq (eE e).1]
        exact (quotEdge_eq_iff _ _).2 ⟨gg e, rfl⟩
    have hwidth : ∀ e, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G (δ e)) : ℤ) :=
      fun e => stabWidth_coe_eq' 𝒯 hfin (δ e) _ (hδcls e)

    have hidx : ∀ (y : W) (hy : 𝒯.Adj x y),
        ∃ e : E, Da e = v ∧ ∃ h : MulAction.stabilizer G x, (h : G) • δ e = (⟨(x, y), hy⟩ : 𝒯.Dart) := by
      intro y hy
      set d : 𝒯.Dart := ⟨(x, y), hy⟩ with hd
      have hq : τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = 0 := by
        rw [colour_out_fst τ hτ hadj]; exact hx0
      set e : E := eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, hq⟩ with he
      have heE : (eE e).1 = Quotient.mk (orbitRel G 𝒯.Dart) d := by rw [he, Equiv.apply_symm_apply]
      have hcl : Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = Quotient.mk (orbitRel G 𝒯.Dart) d := by rw [hδcls, heE]
      obtain ⟨g, hg⟩ := (quotEdge_eq_iff _ _).1 hcl
      have he2 : Da e = v := by
        obtain ⟨g', hg'⟩ := exists_smul_eq_out (G := G) d
        have hout : (eE e).1.out = g' • d := by rw [heE]; exact hg'.symm
        show Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.fst = Quotient.mk (orbitRel G W) x
        rw [hout, smul_dart_fst]
        exact (quotVert_eq_iff _ _).2 ⟨g', rfl⟩
      refine ⟨e, he2, ⟨g⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff]
        have := hδfst e he2
        rw [← hg, smul_dart_fst] at this
        exact this.symm
      · show g⁻¹ • δ e = d
        rw [← hg, inv_smul_smul]
    set T : Finset (E × MulAction.stabilizer G x) := (Finset.univ.filter (fun e => Da e = v)) ×ˢ Finset.univ with hT
    set f : E × MulAction.stabilizer G x → W := fun t => ((t.2 : G) • δ t.1).snd with hf
    have hTmem : ∀ t : E × MulAction.stabilizer G x, t ∈ T ↔ Da t.1 = v := by
      intro t; rw [hT, Finset.mem_product, Finset.mem_filter]; simp
    have hfst : ∀ t ∈ T, ((t.2 : G) • δ t.1).fst = x := by
      intro t ht; rw [smul_dart_fst, hδfst t.1 ((hTmem t).1 ht)]; exact t.2.2
    have hmaps : ∀ t ∈ T, f t ∈ S := by
      intro t ht
      rw [hS]
      have hadj' := ((t.2 : G) • δ t.1).adj
      rw [hfst t ht] at hadj'
      exact hadj'
    have hfib_idx : ∀ t ∈ T, ∀ t' ∈ T, f t = f t' → t.1 = t'.1 := by
      intro t ht t' ht' hff
      have hdd : (t.2 : G) • δ t.1 = (t'.2 : G) • δ t'.1 :=
        SimpleGraph.Dart.ext _ _ (Prod.ext ((hfst t ht).trans (hfst t' ht').symm) (by rw [hf] at hff; exact hff))
      have hcls : (eE t.1).1 = (eE t'.1).1 := by
        rw [← hδcls t.1, ← hδcls t'.1]
        apply (quotEdge_eq_iff _ _).2
        exact ⟨(t.2 : G)⁻¹ * t'.2, by rw [mul_smul, ← hdd, inv_smul_smul]⟩
      exact eE.injective (Subtype.ext hcls)
    have hfib_card : ∀ t ∈ T,
        ((T.filter fun t' => f t' = f t).card : ℤ) = Nat.card (MulAction.stabilizer G (δ t.1)) := by
      intro t ht
      have he2 : Da t.1 = v := (hTmem t).1 ht
      have hset : (T.filter fun t' => f t' = f t) =
          (({t.1} : Finset E) ×ˢ (Finset.univ.filter fun h : MulAction.stabilizer G x =>
            (h : G) • δ t.1 = (t.2 : G) • δ t.1)) := by
        ext t'
        constructor
        · intro hmem
          rw [Finset.mem_filter] at hmem
          obtain ⟨ht', hff⟩ := hmem
          have hee : t'.1 = t.1 := hfib_idx t' ht' t ht hff
          rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter]
          refine ⟨hee, Finset.mem_univ _, ?_⟩
          have hdd : (t'.2 : G) • δ t'.1 = (t.2 : G) • δ t.1 :=
            SimpleGraph.Dart.ext _ _ (Prod.ext ((hfst t' ht').trans (hfst t ht).symm) hff)
          rw [hee] at hdd
          exact hdd
        · intro hmem
          rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at hmem
          obtain ⟨hee, -, hh⟩ := hmem
          rw [Finset.mem_filter]
          refine ⟨(hTmem t').2 (by rw [hee]; exact he2), ?_⟩
          show ((t'.2 : G) • δ t'.1).snd = ((t.2 : G) • δ t.1).snd
          rw [hee, hh]
      rw [hset, Finset.card_product, Finset.card_singleton, one_mul, card_filter_smul_eq' (δ t.1) t.2]
      haveI := finite_stabilizer_dart' 𝒯 hfin (δ t.1)
      rw [← Nat.card_eq_fintype_card]
      congr 1
      refine Nat.card_congr ?_
      refine
        { toFun := fun s => ⟨(s.1 : G), by rw [MulAction.mem_stabilizer_iff]; exact s.2⟩
          invFun := fun s => ⟨⟨s.1, ?_⟩, s.2⟩
          left_inv := fun s => rfl
          right_inv := fun s => rfl }
      rw [MulAction.mem_stabilizer_iff]
      have h1 := congrArg (fun d : 𝒯.Dart => d.fst) s.2
      rw [smul_dart_fst, hδfst t.1 he2] at h1
      exact h1

    have hFval : ∀ t₀ ∈ T, F (f t₀) = ((stabWidth G 𝒯 (eE t₀.1).1 : ℕ) : ℤ) * c t₀.1 := by
      intro t₀ ht₀
      have hy : 𝒯.Adj x (f t₀) := (hS _).1 (hmaps t₀ ht₀)
      simp only [hF, dif_pos hy]
      have hdart : (⟨(x, f t₀), hy⟩ : 𝒯.Dart) = (t₀.2 : G) • δ t₀.1 :=
        SimpleGraph.Dart.ext _ _ (Prod.ext (hfst t₀ ht₀).symm rfl)
      have hcls : Quotient.mk (orbitRel G 𝒯.Dart) (⟨(x, f t₀), hy⟩ : 𝒯.Dart) = (eE t₀.1).1 := by
        rw [hdart, ← hδcls t₀.1]
        exact (quotEdge_eq_iff _ _).2 ⟨(t₀.2 : G), rfl⟩
      have hidx' : ∀ e : E, dartIndex 𝒯 (eE e).1 ⟨(x, f t₀), hy⟩ = if e = t₀.1 then 1 else 0 := by
        intro e
        rw [dartIndex_of_fst_eq_zero 𝒯 τ hτ hadj eE _ hx0, hcls]
        by_cases hee : e = t₀.1
        · rw [if_pos hee, if_pos (by rw [hee])]
        · rw [if_neg hee, if_neg (fun h => hee (eE.injective (Subtype.ext h.symm)))]
      simp_rw [hidx']
      rw [Finset.sum_eq_single t₀.1]
      · simp
      · intro e _ he; rw [if_neg he, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

    have hA : ∑ t ∈ T, c t.1 = (Fintype.card (MulAction.stabilizer G x) : ℤ) *
        ∑ e ∈ Finset.univ.filter (fun e => Da e = v), c e := by
      rw [hT, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have himage : T.image f = S := by
      ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact hmaps t ht
      · intro hy
        obtain ⟨e, he2, h, hh⟩ := hidx y ((hS y).1 hy)
        refine ⟨(e, h), (hTmem _).2 he2, ?_⟩
        rw [hf]; show ((h : G) • δ e).snd = y
        rw [hh]
    have hB : ∑ t ∈ T, c t.1 = ∑ y ∈ S, F y := by
      rw [← himage, ← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image f) (g := f) (fun t ht => Finset.mem_image_of_mem f ht)]
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 hy
      have h1 : ∑ t ∈ T.filter (fun t => f t = f t₀), c t.1 = ∑ t ∈ T.filter (fun t => f t = f t₀), c t₀.1 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_filter] at ht
        rw [hfib_idx t ht.1 t₀ ht₀ ht.2]
      rw [h1, Finset.sum_const, nsmul_eq_mul, hfib_card t₀ ht₀, ← hwidth, hFval t₀ ht₀]
    rw [← hB, hA, hca, mul_zero]
  ·
    have hx1' : τ x ≠ 0 := by rw [hx1]; exact one_ne_zero
    have hex : ∀ e : E, Db e = v → ∃ g : G, g • (eE e).1.out.snd = x := by
      intro e he
      have he' : Quotient.mk (orbitRel G W) x = Quotient.mk (orbitRel G W) (eE e).1.out.snd := by
        rw [hv] at he; simp only [hDb] at he; exact he.symm
      exact (quotVert_eq_iff _ _).1 he'
    choose! gg hgg using hex
    obtain ⟨δ, hδsnd, hδcls⟩ : ∃ δ : E → 𝒯.Dart, (∀ e, Db e = v → (δ e).snd = x) ∧
        (∀ e, Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = (eE e).1) := by
      refine ⟨fun e => gg e • (eE e).1.out, fun e he => ?_, fun e => ?_⟩
      · rw [smul_dart_snd, hgg e he]
      · rw [← Quotient.out_eq (eE e).1]
        exact (quotEdge_eq_iff _ _).2 ⟨gg e, rfl⟩
    have hwidth : ∀ e, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) = (Nat.card (MulAction.stabilizer G (δ e)) : ℤ) :=
      fun e => stabWidth_coe_eq' 𝒯 hfin (δ e) _ (hδcls e)
    have hidx : ∀ (y : W) (hy : 𝒯.Adj x y),
        ∃ e : E, Db e = v ∧ ∃ h : MulAction.stabilizer G x, (h : G) • δ e = (⟨(y, x), hy.symm⟩ : 𝒯.Dart) := by
      intro y hy
      set d : 𝒯.Dart := ⟨(y, x), hy.symm⟩ with hd
      have hy0 : τ y = 0 := by
        rcases zmod2_cases (τ y) with h | h
        · exact h
        · exact absurd (hx1.trans h.symm) (hadj _ _ hy)
      have hq : τ (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out.fst = 0 := by
        rw [colour_out_fst τ hτ hadj]; exact hy0
      set e : E := eE.symm ⟨Quotient.mk (orbitRel G 𝒯.Dart) d, hq⟩ with he
      have heE : (eE e).1 = Quotient.mk (orbitRel G 𝒯.Dart) d := by rw [he, Equiv.apply_symm_apply]
      have hcl : Quotient.mk (orbitRel G 𝒯.Dart) (δ e) = Quotient.mk (orbitRel G 𝒯.Dart) d := by rw [hδcls, heE]
      obtain ⟨g, hg⟩ := (quotEdge_eq_iff _ _).1 hcl
      have he2 : Db e = v := by
        obtain ⟨g', hg'⟩ := exists_smul_eq_out (G := G) d
        have hout : (eE e).1.out = g' • d := by rw [heE]; exact hg'.symm
        show Quotient.mk (MulAction.orbitRel G W) (eE e).1.out.snd = Quotient.mk (orbitRel G W) x
        rw [hout, smul_dart_snd]
        exact (quotVert_eq_iff _ _).2 ⟨g', rfl⟩
      refine ⟨e, he2, ⟨g⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, inv_smul_eq_iff]
        have := hδsnd e he2
        rw [← hg, smul_dart_snd] at this
        exact this.symm
      · show g⁻¹ • δ e = d
        rw [← hg, inv_smul_smul]
    set T : Finset (E × MulAction.stabilizer G x) := (Finset.univ.filter (fun e => Db e = v)) ×ˢ Finset.univ with hT
    set f : E × MulAction.stabilizer G x → W := fun t => ((t.2 : G) • δ t.1).fst with hf
    have hTmem : ∀ t : E × MulAction.stabilizer G x, t ∈ T ↔ Db t.1 = v := by
      intro t; rw [hT, Finset.mem_product, Finset.mem_filter]; simp
    have hsnd : ∀ t ∈ T, ((t.2 : G) • δ t.1).snd = x := by
      intro t ht; rw [smul_dart_snd, hδsnd t.1 ((hTmem t).1 ht)]; exact t.2.2
    have hmaps : ∀ t ∈ T, f t ∈ S := by
      intro t ht
      rw [hS]
      have hadj' := ((t.2 : G) • δ t.1).adj
      rw [hsnd t ht] at hadj'
      exact hadj'.symm
    have hfib_idx : ∀ t ∈ T, ∀ t' ∈ T, f t = f t' → t.1 = t'.1 := by
      intro t ht t' ht' hff
      have hdd : (t.2 : G) • δ t.1 = (t'.2 : G) • δ t'.1 :=
        SimpleGraph.Dart.ext _ _ (Prod.ext (by rw [hf] at hff; exact hff) ((hsnd t ht).trans (hsnd t' ht').symm))
      have hcls : (eE t.1).1 = (eE t'.1).1 := by
        rw [← hδcls t.1, ← hδcls t'.1]
        apply (quotEdge_eq_iff _ _).2
        exact ⟨(t.2 : G)⁻¹ * t'.2, by rw [mul_smul, ← hdd, inv_smul_smul]⟩
      exact eE.injective (Subtype.ext hcls)
    have hfib_card : ∀ t ∈ T,
        ((T.filter fun t' => f t' = f t).card : ℤ) = Nat.card (MulAction.stabilizer G (δ t.1)) := by
      intro t ht
      have he2 : Db t.1 = v := (hTmem t).1 ht
      have hset : (T.filter fun t' => f t' = f t) =
          (({t.1} : Finset E) ×ˢ (Finset.univ.filter fun h : MulAction.stabilizer G x =>
            (h : G) • δ t.1 = (t.2 : G) • δ t.1)) := by
        ext t'
        constructor
        · intro hmem
          rw [Finset.mem_filter] at hmem
          obtain ⟨ht', hff⟩ := hmem
          have hee : t'.1 = t.1 := hfib_idx t' ht' t ht hff
          rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter]
          refine ⟨hee, Finset.mem_univ _, ?_⟩
          have hdd : (t'.2 : G) • δ t'.1 = (t.2 : G) • δ t.1 :=
            SimpleGraph.Dart.ext _ _ (Prod.ext hff ((hsnd t' ht').trans (hsnd t ht).symm))
          rw [hee] at hdd
          exact hdd
        · intro hmem
          rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_filter] at hmem
          obtain ⟨hee, -, hh⟩ := hmem
          rw [Finset.mem_filter]
          refine ⟨(hTmem t').2 (by rw [hee]; exact he2), ?_⟩
          show ((t'.2 : G) • δ t'.1).fst = ((t.2 : G) • δ t.1).fst
          rw [hee, hh]
      rw [hset, Finset.card_product, Finset.card_singleton, one_mul, card_filter_smul_eq' (δ t.1) t.2]
      haveI := finite_stabilizer_dart' 𝒯 hfin (δ t.1)
      rw [← Nat.card_eq_fintype_card]
      congr 1
      refine Nat.card_congr ?_
      refine
        { toFun := fun s => ⟨(s.1 : G), by rw [MulAction.mem_stabilizer_iff]; exact s.2⟩
          invFun := fun s => ⟨⟨s.1, ?_⟩, s.2⟩
          left_inv := fun s => rfl
          right_inv := fun s => rfl }
      rw [MulAction.mem_stabilizer_iff]
      have h1 := congrArg (fun d : 𝒯.Dart => d.snd) s.2
      rw [smul_dart_snd, hδsnd t.1 he2] at h1
      exact h1

    have hFval : ∀ t₀ ∈ T, F (f t₀) = -(((stabWidth G 𝒯 (eE t₀.1).1 : ℕ) : ℤ) * c t₀.1) := by
      intro t₀ ht₀
      have hy : 𝒯.Adj x (f t₀) := (hS _).1 (hmaps t₀ ht₀)
      simp only [hF, dif_pos hy]
      have hdart : (⟨(x, f t₀), hy⟩ : 𝒯.Dart).symm = (t₀.2 : G) • δ t₀.1 :=
        SimpleGraph.Dart.ext _ _ (Prod.ext rfl (hsnd t₀ ht₀).symm)
      have hcls : Quotient.mk (orbitRel G 𝒯.Dart) (⟨(x, f t₀), hy⟩ : 𝒯.Dart).symm = (eE t₀.1).1 := by
        rw [hdart, ← hδcls t₀.1]
        exact (quotEdge_eq_iff _ _).2 ⟨(t₀.2 : G), rfl⟩
      have hidx' : ∀ e : E, dartIndex 𝒯 (eE e).1 ⟨(x, f t₀), hy⟩ = -(if e = t₀.1 then 1 else 0) := by
        intro e
        rw [dartIndex_of_fst_ne_zero 𝒯 τ hτ hadj eE _ hx1', hcls]
        by_cases hee : e = t₀.1
        · rw [if_pos hee, if_pos (by rw [hee])]
        · rw [if_neg hee, if_neg (fun h => hee (eE.injective (Subtype.ext h.symm)))]
      simp_rw [hidx']
      rw [Finset.sum_eq_single t₀.1]
      · simp
      · intro e _ he; rw [if_neg he, neg_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hA : ∑ t ∈ T, c t.1 = (Fintype.card (MulAction.stabilizer G x) : ℤ) *
        ∑ e ∈ Finset.univ.filter (fun e => Db e = v), c e := by
      rw [hT, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have himage : T.image f = S := by
      ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact hmaps t ht
      · intro hy
        obtain ⟨e, he2, h, hh⟩ := hidx y ((hS y).1 hy)
        refine ⟨(e, h), (hTmem _).2 he2, ?_⟩
        rw [hf]; show ((h : G) • δ e).fst = y
        rw [hh]
    have hB : ∑ t ∈ T, c t.1 = ∑ y ∈ S, -F y := by
      rw [← himage, ← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image f) (g := f) (fun t ht => Finset.mem_image_of_mem f ht)]
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 hy
      have h1 : ∑ t ∈ T.filter (fun t => f t = f t₀), c t.1 = ∑ t ∈ T.filter (fun t => f t = f t₀), c t₀.1 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_filter] at ht
        rw [hfib_idx t ht.1 t₀ ht₀ ht.2]
      rw [h1, Finset.sum_const, nsmul_eq_mul, hfib_card t₀ ht₀, ← hwidth, hFval t₀ ht₀, neg_neg]
    have : ∑ y ∈ S, F y = -∑ t ∈ T, c t.1 := by rw [hB, Finset.sum_neg_distrib, neg_neg]
    rw [this, hA, hcb, mul_zero, neg_zero]

end Star
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end FTW
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end E3sec
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section P0sec
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega"

namespace FTW0

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
  {G : Type} [Group G]

theorem theta_self_left [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) (a z₀ z : K)
    (hza : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) :
    theta ρ a a z₀ z = 1 := by
  unfold theta
  have : thetaFactor ρ a a z₀ z = fun _ => 1 := by
    funext γ
    unfold thetaFactor crossRatio
    have h1 : z - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 (hza γ).symm
    have h2 : z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 (hz₀a γ).symm
    exact div_self (mul_ne_zero h1 h2)
  rw [this, tprod_one]

theorem theta_smul_smul_eq [TopologicalSpace K] (ρ : G →* PGL(2, K₀)) {a a' : K}
    (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K) (z₀ z : K) (α : G) :
    theta ρ (pmoebius K₀ (ρ α) a') (pmoebius K₀ (ρ α) a) z₀ z = theta ρ a' a z₀ z := by
  unfold theta
  have hfun : thetaFactor ρ (pmoebius K₀ (ρ α) a') (pmoebius K₀ (ρ α) a) z₀ z =
      (thetaFactor ρ a' a z₀ z) ∘ (fun γ => γ * α) := by
    funext γ
    simp only [Function.comp_apply, thetaFactor, map_mul, pmoebius_mul K₀ ha, pmoebius_mul K₀ ha']
  rw [hfun]
  exact (Equiv.mulRight α).tprod_eq (thetaFactor ρ a' a z₀ z)

theorem theta_unit_eq_of_admissible
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a a' z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀)
    (hza : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z) (hza' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z) (α : G) :
    theta ρ a (pmoebius K₀ (ρ α) a) z₀ z = theta ρ a' (pmoebius K₀ (ρ α) a') z₀ z := by
  have hαa : pmoebius K₀ (ρ α) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha (ρ α)
  have hαa' : pmoebius K₀ (ρ α) a' ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha' (ρ α)
  have M := fun (x y : K) (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) =>
    thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex ρ hρ hx hy hz₀ hz

  have hzαa' : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a') ≠ z := fun γ => by
    rw [← pmoebius_mul K₀ ha', ← map_mul]; exact hza' (γ * α)
  have hz₀αa' : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a') ≠ z₀ := fun γ => by
    rw [← pmoebius_mul K₀ ha', ← map_mul]; exact hz₀a' (γ * α)

  have e1 := theta_mul_theta_eq_theta ρ (a := a) (b := a') (c := pmoebius K₀ (ρ α) a) hza' hz₀a'
    (M _ _ ha ha') (M _ _ ha' hαa)
  have e2 := theta_mul_theta_eq_theta ρ (a := a') (b := pmoebius K₀ (ρ α) a') (c := pmoebius K₀ (ρ α) a)
    hzαa' hz₀αa' (M _ _ ha' hαa') (M _ _ hαa' hαa)

  have e3 := theta_smul_smul_eq ρ ha ha' z₀ z α
  have e4 := theta_mul_theta_eq_theta ρ (a := a) (b := a') (c := a) hza' hz₀a' (M _ _ ha ha') (M _ _ ha' ha)
  rw [theta_self_left ρ a z₀ z hza hz₀a] at e4
  rw [← e1, ← e2, e3]
  calc theta ρ a a' z₀ z * (theta ρ a' (pmoebius K₀ (ρ α) a') z₀ z * theta ρ a' a z₀ z)
      = theta ρ a' (pmoebius K₀ (ρ α) a') z₀ z * (theta ρ a a' z₀ z * theta ρ a' a z₀ z) := by ring
    _ = theta ρ a' (pmoebius K₀ (ρ α) a') z₀ z := by rw [e4, mul_one]

end FTW0
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end P0sec
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section GENsec
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega"

namespace EPVgen

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {G : Type} [Group G]

theorem finite_setOf_mem_affinoid_and_exists_pmoebius_eq
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (g : PGL(2, K₀)) (n : ℕ) {y : K} (hy : y ∈ upperHalfPlane K₀ K) :
    {ζ : K | ζ ∈ affinoid ϖ n ∧ ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g ζ}.Finite := by
  obtain ⟨m, hm⟩ := exists_mapsTo_affinoid ϖ g n
  obtain ⟨m', hm'⟩ := hex y hy
  set N := max m m' with hN
  have hyN : y ∈ affinoid ϖ N := affinoid_mono ϖ (le_max_right _ _) hm'
  have hfin := finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ N hyN
  refine (hfin.image fun γ => pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y)).subset ?_
  rintro ζ ⟨hζ, γ, hγ⟩
  have hζΩ : ζ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hζ
  refine ⟨γ, ?_, ?_⟩
  · show pmoebius K₀ (ρ γ) y ∈ affinoid ϖ N
    rw [hγ]; exact affinoid_mono ϖ (le_max_left _ _) (hm hζ)
  · show pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y) = ζ
    rw [hγ, ← pmoebius_mul K₀ hζΩ, inv_mul_cancel, pmoebius_one]

theorem exists_mem_ball_forall_ne
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (g : PGL(2, K₀)) (n : ℕ) {x₀ c : K} (hc : c ≠ 0)
    (hball : ∀ ζ : K, Valued.v (ζ - x₀) < Valued.v c → ζ ∈ affinoid ϖ n)
    (Y : Finset K) (hY : ∀ y ∈ Y, y ∈ upperHalfPlane K₀ K) (B : Finset K) :
    ∃ ζ : K, Valued.v (ζ - x₀) < Valued.v c ∧ ζ ∉ B ∧
      ∀ y ∈ Y, ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ pmoebius K₀ g ζ := by
  classical

  have hbad : {ζ : K | ζ ∈ affinoid ϖ n ∧ ∃ y ∈ Y, ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g ζ}.Finite := by
    refine (Set.Finite.biUnion (Finset.finite_toSet Y) fun y hy =>
      finite_setOf_mem_affinoid_and_exists_pmoebius_eq ϖ hex ρ hρ g n (hY y hy)).subset ?_
    rintro ζ ⟨hζ, y, hy, γ, hγ⟩
    exact Set.mem_biUnion hy ⟨hζ, γ, hγ⟩

  have hp0 : algebraMap K₀ K ϖ.ϖ ≠ 0 := (Valuation.ne_zero_iff _).1 ϖ.pos.ne'
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  let s : ℕ → K := fun k => x₀ + c * algebraMap K₀ K ϖ.ϖ ^ (k + 1)
  have hs_inj : Function.Injective s := by
    intro i j hij
    have h1 := mul_left_cancel₀ hc (add_left_cancel hij)
    have h2 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (i + 1) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (j + 1) := by
      have := congrArg (Valued.v (R := K) (Γ₀ := Γ₀)) h1
      simpa only [Valuation.map_pow] using this
    exact Nat.succ_injective (pow_right_injective₀ ϖ.pos hp1.ne h2)
  have hs_ball : ∀ k, Valued.v (s k - x₀) < Valued.v c := fun k => by
    show Valued.v (x₀ + c * algebraMap K₀ K ϖ.ϖ ^ (k + 1) - x₀) < Valued.v c
    rw [add_sub_cancel_left, map_mul, map_pow]
    exact mul_lt_of_lt_one_right ((Valuation.pos_iff _).2 hc) (pow_lt_one₀ zero_le' hp1 (Nat.succ_ne_zero k))
  have hinf : {ζ : K | Valued.v (ζ - x₀) < Valued.v c}.Infinite :=
    Set.infinite_of_injective_forall_mem hs_inj hs_ball
  obtain ⟨ζ, hζ, hζnot⟩ := (hinf.diff (hbad.union (Finset.finite_toSet B))).nonempty
  refine ⟨ζ, hζ, fun hB => hζnot (Or.inr hB), fun y hy γ hγ => hζnot (Or.inl ⟨hball ζ hζ, y, hy, γ, hγ⟩)⟩

end EPVgen
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end GENsec
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section ORBsec
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford"

namespace Orb

section

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]

theorem pmoebius_mk_one (z : K) : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (1 : GL (Fin 2) K₀)) z = z := by
  rw [map_one, pmoebius_one]

theorem pmoebius_rho_mul {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (γ δ : G) {z : K}
    (hz : z ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (ρ (γ * δ)) z = pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ δ) z) := by
  rw [map_mul, pmoebius_mul K₀ hz]

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

section

variable (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]

theorem mk_smul_vertex (h : GL (Fin 2) K₀) (v : LT.LatticeTree.Vertex R K₀) :
    Matrix.ProjGenLinGroup.mk h • v = h • v :=
  BruhatTits.pgl_mk_smul h v

theorem smul_vertex_eq_of_mk_eq {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)] (hρ : ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (γ : G) (h : GL (Fin 2) K₀) (hh : Matrix.ProjGenLinGroup.mk h = ρ γ) (v : LT.LatticeTree.Vertex R K₀) :
    γ • v = h • v := by
  rw [hρ γ v, ← hh, BruhatTits.pgl_mk_smul]

theorem ne_of_colour_ne (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)] [GraphAction G (BruhatTits.tree R K₀)]
    (hρ : ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (gx : GL (Fin 2) K₀) (hcol : τ (gx • LT.LatticeTree.stdVertex R K₀) ≠ τ (LT.LatticeTree.stdVertex R K₀))
    (a' : K) (ha' : a' ∈ affinoid ϖ₁ 0) (u : K) (hu : u ∈ affinoid ϖ₁ 0) (γ : G) :
    pmoebius K₀ (ρ γ) a' ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk gx) u := by
  intro heq
  obtain ⟨h, hh⟩ := Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
  have hΩa : a' ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 ha'
  have hΩu : u ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ₁ 0 hu
  have hx1 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk gx)⁻¹ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gx) u) = u := by
    rw [← pmoebius_mul K₀ hΩu, inv_mul_cancel, pmoebius_one]
  have hx2 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk h)⁻¹ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gx) u) = a' := by
    rw [← heq, hh, ← pmoebius_mul K₀ hΩa, inv_mul_cancel, pmoebius_one]
  have hvert := smul_stdVertex_eq_of_mem_affinoid_zero R K₀ ϖ hϖ K hint hv ϖ₁ gx h
    (by rw [hx1]; exact hu) (by rw [hx2]; exact ha')
  apply hcol
  rw [hvert, ← BruhatTits.pgl_mk_smul, hh, ← hρ γ, hτ]

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end Orb
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end ORBsec
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

open FTWcore in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    [DecidableEq (LT.LatticeTree.Vertex R K₀)]

    (a : K) (ha : a ∈ upperHalfPlane K₀ K) (α : G)
    (z₀ : K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀)

    (g g' : GL (Fin 2) K₀) (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0)
    (hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w)
    (hw'a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w')
    (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g • LT.LatticeTree.stdVertex R K₀) (g' • LT.LatticeTree.stdVertex R K₀)) :
    Valued.v (theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w')) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
          (∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
              (LT.LatticeTree.stdVertex R K₀) α e *
            CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p e) =
      Valued.v (theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w)) := by
  classical
  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hqdef
  have hq0 : 0 < q := CerednikDrinfeld.Omega.GlobalCurrent.v_algebraMap_pos hϖ
  have hq1 : q < 1 := CerednikDrinfeld.Omega.GlobalCurrent.v_algebraMap_lt_one hϖ hv
  have hqne : q ≠ 0 := hq0.ne'
  have hqinj : ∀ m n : ℤ, q ^ m = q ^ n → m = n := fun m n h => zpow_right_injective₀ hq0 hq1.ne h
  have hΩ0 : ∀ {u : K}, u ∈ affinoid ϖ₁ 0 → u ∈ upperHalfPlane K₀ K := fun hu => affinoid_subset_upperHalfPlane ϖ₁ 0 hu
  have hρmul : ∀ (γ δ : G) (z : K), z ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (γ * δ)) z = pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ δ) z) := by
    intro γ δ z hz; rw [map_mul, pmoebius_mul K₀ hz]

  have orbit_symm : ∀ {y a' : K}, a' ∈ upperHalfPlane K₀ K → (∀ γ : G, pmoebius K₀ (ρ γ) y ≠ a') →
      ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ y := by
    intro y a' ha' h γ heq
    apply h γ⁻¹
    rw [← heq, ← hρmul γ⁻¹ γ a' ha', inv_mul_cancel, map_one, pmoebius_one]

  have hdisc : IsDiscrete K ρ := by
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ ?_
    have hset : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀} =
        ((MulAction.stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G) := by
      ext γ
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      rw [← hρ γ (LT.LatticeTree.stdVertex R K₀)]
    rw [hset]
    haveI := hfin (LT.LatticeTree.stdVertex R K₀)
    exact Set.toFinite _

  have hball : ∀ ζ : K, Valued.v (ζ - w) < Valued.v (1 : K) → ζ ∈ affinoid ϖ₁ 0 := by
    intro ζ hζ
    rw [map_one] at hζ
    obtain ⟨hw1, hw2⟩ := (mem_affinoid_iff' ϖ₁ 0 w).1 hw
    rw [pow_zero] at hw1 hw2
    rw [mem_affinoid_iff', pow_zero, pow_zero]
    have e1 : ζ = (ζ - w) + w := by ring
    refine ⟨?_, fun a₀ => ?_⟩
    · rw [e1]; exact (Valuation.map_add _ _ _).trans (max_le hζ.le hw1)
    · have e2 : ζ - algebraMap K₀ K a₀ = (w - algebraMap K₀ K a₀) + (ζ - w) := by ring
      rw [e2, Valuation.map_add_eq_of_lt_left _ (hζ.trans_le (hw2 a₀))]; exact hw2 a₀
  obtain ⟨a', ha'ball, -, ha'Y⟩ := EPVgen.exists_mem_ball_forall_ne ϖ₁ hex ρ hdisc (1 : PGL(2, K₀)) 0 (one_ne_zero) hball
    ({z₀, a, pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w, pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w'} : Finset K)
    (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hz₀
      · exact ha
      · exact pmoebius_mem_upperHalfPlane K₀ (hΩ0 hw) _
      · exact pmoebius_mem_upperHalfPlane K₀ (hΩ0 hw') _) ∅
  simp only [pmoebius_one] at ha'Y
  have ha'0 : a' ∈ affinoid ϖ₁ 0 := hball a' ha'ball
  have ha' : a' ∈ upperHalfPlane K₀ K := hΩ0 ha'0
  have hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀ := orbit_symm ha' (ha'Y z₀ (by simp))
  have haa' : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ a' := ha'Y a (by simp)
  have hga' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w :=
    orbit_symm ha' (ha'Y _ (by simp))
  have hg'a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w' :=
    orbit_symm ha' (ha'Y _ (by simp))

  obtain ⟨U, hU, -, hUθ, -⟩ := CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
    K₀ K ϖ₁ hex ρ hdisc ha' hz₀ hz₀a' α

  set P : PseudoUniformizer K₀ K := CerednikDrinfeld.Omega.GlobalCurrent.treePseudoUniformizer (K := K) hϖ hint hv with hPdef
  have hP : P.ϖ = algebraMap R K₀ ϖ := rfl
  obtain ⟨hhol, haff⟩ := CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq ϖ₁ P
  let F : ↥(holRing P) := ⟨(U : ↥(upperHalfPlane K₀ K) → K), hhol ▸ U.2⟩
  have hF : IsUnit F := by
    obtain ⟨V, hUV⟩ := hU.exists_right_inv
    refine isUnit_iff_exists_inv.mpr ⟨⟨(V : ↥(upperHalfPlane K₀ K) → K), hhol ▸ V.2⟩, ?_⟩
    have h1 := congrArg Subtype.val hUV
    exact Subtype.ext h1
  obtain ⟨Φ, μ, hΦ0, hchart, hjump, hanti, hkir⟩ :=
    Cur.exists_potential R K₀ ϖ hϖ K hint hv hq hrk P hP F hF
  have hchart' : ∀ (gg : GL (Fin 2) K₀) (u : K) (hu : u ∈ affinoid ϖ₁ 0),
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk gg • ⟨u, hΩ0 hu⟩)) =
        Φ (gg • LT.LatticeTree.stdVertex R K₀) := by
    intro gg u hu
    exact hchart gg u (haff ▸ hu)

  let A : E → ℤ := fun e => ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
    pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) α e
  let Wt : LT.LatticeTree.Vertex R K₀ → LT.LatticeTree.Vertex R K₀ → ℤ := fun x y =>
    if h : (BruhatTits.tree R K₀).Adj x y then ∑ e, A e * dartIndex (BruhatTits.tree R K₀) (eE e).1 ⟨(x, y), h⟩ else 0
  have hWt_adj : ∀ (x y : LT.LatticeTree.Vertex R K₀) (h : (BruhatTits.tree R K₀).Adj x y),
      Wt x y = ∑ e, A e * dartIndex (BruhatTits.tree R K₀) (eE e).1 ⟨(x, y), h⟩ := fun x y h => by
    simp only [Wt, dif_pos h]
  have hWanti : ∀ x y, (BruhatTits.tree R K₀).Adj x y → Wt y x = -Wt x y := by
    intro x y h
    rw [hWt_adj x y h, hWt_adj y x h.symm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [show (⟨(y, x), h.symm⟩ : (BruhatTits.tree R K₀).Dart) = (⟨(x, y), h⟩ : (BruhatTits.tree R K₀).Dart).symm from rfl,
      dartIndex_symm, mul_neg]
  have hWt_walk : ∀ {x y : LT.LatticeTree.Vertex R K₀} (pp : (BruhatTits.tree R K₀).Walk x y),
      ∑ e, A e * walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) pp e = dartSum Wt pp := by
    intro x y pp
    induction pp with
    | nil => simp [walkCycle_nil]
    | cons h pp ih =>
      rw [dartSum_cons, hWt_adj _ _ h, ← ih, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by rw [walkCycle_cons, mul_add]

  have htwo : ∀ vtx y y', τ vtx = τ (LT.LatticeTree.stdVertex R K₀) →
      (BruhatTits.tree R K₀).Adj vtx y → (BruhatTits.tree R K₀).Adj vtx y' →
      μ y vtx + μ vtx y' = -(Wt y vtx + Wt vtx y') := by
    intro vtx y y' hc hy hy'
    obtain ⟨gy, hgy⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ y
    obtain ⟨gy', hgy'⟩ := LT.LatticeTree.exists_act_stdVertex_eq R K₀ y'
    have hgyv : gy • LT.LatticeTree.stdVertex R K₀ = y := hgy
    have hgy'v : gy' • LT.LatticeTree.stdVertex R K₀ = y' := hgy'
    subst hgyv hgy'v
    have hcy : τ (gy • LT.LatticeTree.stdVertex R K₀) ≠ τ (LT.LatticeTree.stdVertex R K₀) :=
      fun h => hadj _ _ hy (hc.trans h.symm)
    have hcy' : τ (gy' • LT.LatticeTree.stdVertex R K₀) ≠ τ (LT.LatticeTree.stdVertex R K₀) :=
      fun h => hadj _ _ hy' (hc.trans h.symm)
    have hsep : τ (gy • LT.LatticeTree.stdVertex R K₀) ≠ τ ((1 : GL (Fin 2) K₀) • LT.LatticeTree.stdVertex R K₀) := by
      rw [one_smul]; exact hcy
    have hsep' : τ (gy' • LT.LatticeTree.stdVertex R K₀) ≠ τ ((1 : GL (Fin 2) K₀) • LT.LatticeTree.stdVertex R K₀) := by
      rw [one_smul]; exact hcy'
    let P₂ : (BruhatTits.tree R K₀).Walk (gy • LT.LatticeTree.stdVertex R K₀) (gy' • LT.LatticeTree.stdVertex R K₀) :=
      SimpleGraph.Walk.cons hy.symm (SimpleGraph.Walk.cons hy' SimpleGraph.Walk.nil)
    have key := CerednikDrinfeld.Omega.v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle
      R K₀ ϖ hϖ K hint hv hq ϖ₁ ρ hρ hfin τ hτ hadj eE 1 gy gy' ha'0 ha'0 ha'0 hsep hsep' P₂ α
    rw [Orb.pmoebius_mk_one] at key

    have hxΩ : pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy) a' ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha' _
    have hx'Ω : pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy') a' ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha' _
    have hxa : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy) a' :=
      Orb.ne_of_colour_ne R K₀ ϖ hϖ K hint hv ϖ₁ ρ hρ τ hτ gy hcy a' ha'0 a' ha'0
    have hx'a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy') a' :=
      Orb.ne_of_colour_ne R K₀ ϖ hϖ K hint hv ϖ₁ ρ hρ τ hτ gy' hcy' a' ha'0 a' ha'0
    have hxb : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a') ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy) a' :=
      fun γ => by rw [← hρmul γ α a' ha']; exact hxa (γ * α)
    have hcoc := CerednikDrinfeld.Omega.theta_mul_theta_basePoint ρ hxa hxb
      (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc ha' (pmoebius_mem_upperHalfPlane K₀ ha' _) hz₀ hxΩ)
      (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc ha' (pmoebius_mem_upperHalfPlane K₀ ha' _) hxΩ hx'Ω)
    have hUx : (U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk gy • ⟨a', ha'⟩) =
        theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy) a') :=
      hUθ _ (fun ⟨γ, hγ⟩ => hxa γ hγ)
    have hUx' : (U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk gy' • ⟨a', ha'⟩) =
        theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy') a') :=
      hUθ _ (fun ⟨γ, hγ⟩ => hx'a γ hγ)
    have hΦy : Φ (gy • LT.LatticeTree.stdVertex R K₀) =
        Valued.v (theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy) a')) := by
      rw [← hUx]; exact (hchart' gy a' ha'0).symm
    have hΦy' : Φ (gy' • LT.LatticeTree.stdVertex R K₀) =
        Valued.v (theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gy') a')) := by
      rw [← hUx']; exact (hchart' gy' a' ha'0).symm

    have hrel : Φ (gy' • LT.LatticeTree.stdVertex R K₀) = Φ (gy • LT.LatticeTree.stdVertex R K₀) *
        q ^ (-(∑ e, A e * walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) P₂ e)) := by
      rw [hΦy, hΦy', ← hcoc, map_mul, key]

    have hint2 := potential_walk Φ q hqne μ hjump P₂
    have hexp : dartSum μ P₂ = -(∑ e, A e * walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) P₂ e) := by
      apply hqinj
      have := hint2.symm.trans hrel
      exact mul_left_cancel₀ (hΦ0 _) this
    rw [hWt_walk P₂] at hexp
    have e1 : dartSum μ P₂ = μ (gy • LT.LatticeTree.stdVertex R K₀) vtx + μ vtx (gy' • LT.LatticeTree.stdVertex R K₀) := by
      simp only [P₂, dartSum_cons, dartSum_nil, add_zero]
    have e2 : dartSum Wt P₂ = Wt (gy • LT.LatticeTree.stdVertex R K₀) vtx + Wt vtx (gy' • LT.LatticeTree.stdVertex R K₀) := by
      simp only [P₂, dartSum_cons, dartSum_nil, add_zero]
    rw [e1, e2] at hexp
    exact hexp

  have hK : ∀ vtx, τ vtx = τ (LT.LatticeTree.stdVertex R K₀) →
      ∃ S : Finset (LT.LatticeTree.Vertex R K₀), (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj vtx y) ∧ S.Nonempty ∧
        ∑ y ∈ S, μ vtx y = 0 ∧ ∑ y ∈ S, Wt vtx y = 0 := by
    intro vtx _
    obtain ⟨S, hS⟩ := FTW.exists_neighbourFinset R K₀ ϖ hϖ vtx
    obtain ⟨y₁, hy₁⟩ := FTW.exists_adj R K₀ ϖ hϖ vtx
    refine ⟨S, hS, ⟨y₁, (hS y₁).2 hy₁⟩, hkir vtx S hS, ?_⟩
    have h34 := FTW.sum_weight_dartIndex_eq_zero (BruhatTits.tree R K₀) hfin τ hτ hadj eE
      (pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) α)
      (FTW.pathCycle_mem_ribbonKernel (BruhatTits.tree R K₀) (CerednikDrinfeld.BruhatTits.tree_isTree R K₀) τ hτ hadj eE _ α)
      vtx S hS
    rw [← Finset.sum_attach S]
    rw [← h34]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hWt_adj vtx y.1 ((hS y.1).1 y.2)]

  have hall := FTWcore.eq_neg_of_two_step (BruhatTits.tree R K₀) τ hadj (τ (LT.LatticeTree.stdVertex R K₀)) μ Wt
    (fun x y _ => hanti x y) hWanti htwo hK

  have hintp := potential_walk Φ q hqne μ hjump p
  have hds : dartSum μ p = -dartSum Wt p := dartSum_eq_neg μ Wt hall p

  have hgwΩ : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ (hΩ0 hw) _
  have hg'w'Ω : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w' ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ (hΩ0 hw') _
  have hUg : (U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk g • ⟨w, hΩ0 hw⟩) =
      theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w) :=
    hUθ _ (fun ⟨γ, hγ⟩ => hga' γ hγ)
  have hUg' : (U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk g' • ⟨w', hΩ0 hw'⟩) =
      theta ρ a' (pmoebius K₀ (ρ α) a') z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w') :=
    hUθ _ (fun ⟨γ, hγ⟩ => hg'a' γ hγ)
  have hval : Valued.v (theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w)) =
      Φ (g • LT.LatticeTree.stdVertex R K₀) := by
    rw [FTW0.theta_unit_eq_of_admissible ϖ₁ hex ρ hdisc ha ha' hz₀ hgwΩ hz₀a hz₀a' hwa hga' α, ← hUg]
    exact hchart' g w hw
  have hval' : Valued.v (theta ρ a (pmoebius K₀ (ρ α) a) z₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g') w')) =
      Φ (g' • LT.LatticeTree.stdVertex R K₀) := by
    rw [FTW0.theta_unit_eq_of_admissible ϖ₁ hex ρ hdisc ha ha' hz₀ hg'w'Ω hz₀a hz₀a' hw'a hg'a' α, ← hUg']
    exact hchart' g' w' hw'
  have hsum : (∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
              (LT.LatticeTree.stdVertex R K₀) α e *
            CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p e) = dartSum Wt p := by
    rw [← hWt_walk p]
  rw [hval, hval', hsum, hintp, hds, mul_assoc, ← zpow_add₀ hqne, neg_add_cancel, zpow_zero, mul_one]

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.CerednikDrinfeld.Omega.GlobalCurrent P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq.FTWcore"

end S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq (solution)
