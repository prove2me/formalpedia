-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a9c952a0-45d2-5332-acd6-ae98a7ce9ce0

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
import Theorems.Thm_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.GroupTheory.OrderOfElement
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
import Theorems.Thm_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
import Theorems.Thm_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction"

noncomputable section
namespace UAP

theorem v_apply_eq_of_forall_v_apply_smul_eq
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f)
    (H0 : ∀ (g : GL (Fin 2) K₀)
      (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
      (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩)) :
    ∀ z w : ↥(upperHalfPlane K₀ K),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w) := by
  have hconn := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R K₀).1

  have walk : ∀ g : GL (Fin 2) K₀,
      (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀) :=
    fun g => (hconn.preconnected _ _).some

  have hvert : ∀ (g : GL (Fin 2) K₀) (w : K) (hw : w ∈ affinoid ϖ₁ 0) (y : ↥(upperHalfPlane K₀ K)),
      (y : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w →
      ∀ (w₀ : K) (hw₀ : w₀ ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) y) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩) := by
    intro g w hw y hy w₀ hw₀
    have : y = (Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩ :=
      Subtype.ext (by rw [hy, coe_smul_upperHalfPlane])
    rw [this]
    exact H0 g (walk g) w w₀ hw hw₀

  have hpt : ∀ (z : ↥(upperHalfPlane K₀ K)), ∃ (w₀ : K) (hw₀ : w₀ ∈ affinoid ϖ₁ 0),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) =
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩) := by
    intro z
    obtain ⟨g, g', w, w', y, y', hw, hw', hy, hy', -, hmin, hmax⟩ :=
      CerednikDrinfeld.Omega.exists_adj_min_le_v_apply_le_max_of_isUnit R K₀ ϖ hϖ K hint hv hq ϖ₁ hrk hex f hf z
    refine ⟨w, hw, ?_⟩
    have h1 := hvert g w hw y hy w hw
    have h2 := hvert g' w' hw' y' hy' w hw
    rw [h1, h2, min_self] at hmin
    rw [h1, h2, max_self] at hmax
    exact le_antisymm hmax hmin
  intro z w
  obtain ⟨w₁, hw₁, h₁⟩ := hpt z
  obtain ⟨w₂, hw₂, h₂⟩ := hpt w
  rw [h₁, h₂]

  have h := H0 1 (walk 1) w₁ w₂ hw₁ hw₂
  rwa [map_one, one_smul] at h

theorem v_apply_eq_of_current_eq_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)] [GraphAction G (BruhatTits.tree R K₀)]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2)
    [DecidableEq (QuotEdge G (BruhatTits.tree R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (c : E → ℤ) (hc : c = 0)
    (h2 : ∀ (g : GL (Fin 2) K₀)
        (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
        (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
              (∑ e, c e * walkCycle (BruhatTits.tree R K₀) (fun e => (eE e).1) p e)) :
    ∀ z w : ↥(upperHalfPlane K₀ K),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w) :=
  v_apply_eq_of_forall_v_apply_smul_eq R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex f hf fun g p w w' hw hw' => by
    rw [h2 g p w w' hw hw', hc]
    simp

end UAP

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "DegeneracyData ribbonKernel pgl_mk_smul tree BruhatTits.tree BruhatTits.pgl_mk_smul Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq Omega.exists_adj_min_le_v_apply_le_max_of_isUnit BruhatTits.tree_connected_and_colorable_two"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane mem_affinoid_iff' IsExhausted IsHolOn restrictAffinoid holRing mem_holRing_iff coe_smul_upperHalfPlane coe_smul_holRing_apply pmoebius upperHalfPlane exists_int_neighbours_sum_eq_zero_v_apply_smul_eq pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq exists_adj_min_le_v_apply_le_max_of_isUnit v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one"
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

section HolRingCofinal

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem IsHolOn.comp_inclusion {S S' : Set K} (h : S' ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (f ∘ Set.inclusion h) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  exact ⟨r, fun k z hz => hr k z (h hz), ⟨b, fun k z => hb k (Set.inclusion h z)⟩, hlim.comp (Set.inclusion h)⟩

theorem PseudoUniformizer.ϖ_ne_zero (ϖ : PseudoUniformizer K₀ K) : ϖ.ϖ ≠ 0 := by
  intro h
  have := ϖ.pos
  rw [h, map_zero, Valuation.map_zero] at this
  exact lt_irrefl _ this

theorem exists_affinoid_subset_affinoid (ϖ ϖ' : PseudoUniformizer K₀ K) (n : ℕ) :
    ∃ m : ℕ, affinoid ϖ' n ⊆ affinoid ϖ m := by
  obtain ⟨N, hN, -⟩ := ϖ.scale (ϖ'.ϖ ^ n) (pow_ne_zero n (PseudoUniformizer.ϖ_ne_zero ϖ'))
  rw [map_pow, Valuation.map_pow] at hN

  have hinv : (Valued.v (algebraMap K₀ K ϖ'.ϖ))⁻¹ ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ N := by
    rw [inv_pow, inv_pow]
    exact inv_anti₀ (pow_pos ϖ.pos N) hN
  refine ⟨N, fun z hz => ?_⟩
  rw [mem_affinoid_iff'] at hz ⊢
  exact ⟨hz.1.trans hinv, fun a => hN.trans (hz.2 a)⟩

theorem holRing_le_holRing (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ ≤ holRing ϖ' := by
  intro f hf n
  obtain ⟨m, hm⟩ := exists_affinoid_subset_affinoid ϖ ϖ' n
  exact IsHolOn.comp_inclusion hm (hf m)

theorem holRing_eq_holRing (ϖ ϖ' : PseudoUniformizer K₀ K) : holRing ϖ = holRing ϖ' :=
  le_antisymm (holRing_le_holRing ϖ ϖ') (holRing_le_holRing ϖ' ϖ)

theorem affinoid_zero_eq (ϖa ϖb : PseudoUniformizer K₀ K) : affinoid ϖa 0 = affinoid ϖb 0 := by
  ext z
  simp only [affinoid, pow_zero, Set.mem_setOf_eq]

theorem v_apply_eq_of_isUnit [DecidableEq K] [IsAlgClosed K] (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q))
    (hF : IsUnit F) {w w' : K} (hw : w ∈ affinoid Q 0) (hw' : w' ∈ affinoid Q 0) :
    Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w, affinoid_subset_upperHalfPlane Q 0 hw⟩) =
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane Q 0 hw'⟩) := by
  obtain ⟨G, hFG⟩ := hF.exists_right_inv
  have hprod : restrictAffinoid Q 0 (F : ↥(upperHalfPlane K₀ K) → K) * restrictAffinoid Q 0 (G : ↥(upperHalfPlane K₀ K) → K) = 1 := by
    funext z
    have := congrArg (fun H : ↥(holRing Q) => (H : ↥(upperHalfPlane K₀ K) → K) (Set.inclusion (affinoid_subset_upperHalfPlane Q 0) z)) hFG
    simp at this
    exact this
  exact v_apply_eq_of_mem_holOn_affinoid_zero_of_mul_eq_one Q ((mem_holRing_iff Q _).1 F.2 0) ((mem_holRing_iff Q _).1 G.2 0)
    hprod ⟨w, hw⟩ ⟨w', hw'⟩

end HolRingCofinal

section Translates

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def omegaTranslate (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q)) (g : PGL(2, K₀)) : ↥(holRing Q) := g⁻¹ • F

theorem omegaTranslate_apply (Q : PseudoUniformizer K₀ K) (F : ↥(holRing Q)) (g : PGL(2, K₀)) (z : ↥(upperHalfPlane K₀ K)) :
    (omegaTranslate Q F g : ↥(upperHalfPlane K₀ K) → K) z = (F : ↥(upperHalfPlane K₀ K) → K) (g • z) := by
  rw [omegaTranslate, coe_smul_holRing_apply, inv_inv]

theorem isUnit_omegaTranslate (Q : PseudoUniformizer K₀ K) {F : ↥(holRing Q)} (hF : IsUnit F) (g : PGL(2, K₀)) :
    IsUnit (omegaTranslate Q F g) :=
  hF.map (MulSemiringAction.toRingHom _ ↥(holRing Q) g⁻¹)

end Translates

end CerednikDrinfeld.Omega.GlobalCurrent
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega.GlobalCurrent"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega.GlobalCurrent"

open CerednikDrinfeld.Omega.GlobalCurrent in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)] [GraphAction G (BruhatTits.tree R K₀)]
    (hρ : ActsThrough (LT.LatticeTree.Vertex R K₀) ρ) (hρinj : Function.Injective ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (QuotEdge G (BruhatTits.tree R K₀))] [DecidableEq (QuotVert G (LT.LatticeTree.Vertex R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (f : ↥(holRing ϖ₁)) (hf : IsUnit f) (χ : G →* Kˣ)
    (haut : ∀ (γ : G) (z : ↥(upperHalfPlane K₀ K)),
      (f : ↥(upperHalfPlane K₀ K) → K) ((ρ γ) • z) = ((χ γ : Kˣ) : K) * (f : ↥(upperHalfPlane K₀ K) → K) z)
    (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1) :
    ∃ c : E → ℤ,
      c ∈ ribbonKernel
        (⟨fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
          fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd,
          fun _ => 1⟩ : DegeneracyData E (QuotVert G (LT.LatticeTree.Vertex R K₀))) ∧
      (∀ (g : GL (Fin 2) K₀)
        (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
        (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
              (∑ e, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * c e *
                walkCycle (BruhatTits.tree R K₀) (fun e => (eE e).1) p e)) ∧
      (c = 0 → ∀ z w : ↥(upperHalfPlane K₀ K),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w)) := by
  classical

  set P : PseudoUniformizer K₀ K := treePseudoUniformizer hϖ hint hv with hPdef
  have hP : P.ϖ = algebraMap R K₀ ϖ := rfl
  set F : ↥(holRing P) := ⟨(f : ↥(upperHalfPlane K₀ K) → K), by rw [← holRing_eq_holRing ϖ₁ P]; exact f.2⟩ with hFdef
  have hFf : (F : ↥(upperHalfPlane K₀ K) → K) = (f : ↥(upperHalfPlane K₀ K) → K) := rfl
  have hF : IsUnit F := by
    obtain ⟨g, hfg⟩ := hf.exists_right_inv
    refine isUnit_iff_exists_inv.mpr ⟨⟨(g : ↥(upperHalfPlane K₀ K) → K), by rw [← holRing_eq_holRing ϖ₁ P]; exact g.2⟩, ?_⟩
    exact Subtype.ext (by have := congrArg Subtype.val hfg; exact this)
  have h00 : affinoid ϖ₁ 0 = affinoid P 0 := affinoid_zero_eq ϖ₁ P
  have hfne : ∀ z : ↥(upperHalfPlane K₀ K), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) ≠ 0 := by
    intro z h0
    obtain ⟨g, hfg⟩ := hf.exists_right_inv
    have := congrArg (fun H : ↥(holRing ϖ₁) => (H : ↥(upperHalfPlane K₀ K) → K) z) hfg
    rw [show ((f * g : ↥(holRing ϖ₁)) : ↥(upperHalfPlane K₀ K) → K) z =
      (f : ↥(upperHalfPlane K₀ K) → K) z * (g : ↥(upperHalfPlane K₀ K) → K) z from rfl,
      (Valuation.zero_iff _).1 h0, zero_mul] at this
    exact zero_ne_one this

  set q : Γ₀ := Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) with hqdef
  have hq0 : 0 < q := v_algebraMap_pos hϖ
  have hq1 : q ≠ 1 := (v_algebraMap_lt_one hϖ hv).ne
  have hqinj : Function.Injective (fun k : ℤ => q ^ k) := zpow_right_injective₀ hq0 hq1

  set v₀ : LT.LatticeTree.Vertex R K₀ := LT.LatticeTree.stdVertex R K₀ with hv₀

  have hW : ∀ (g g' : GL (Fin 2) K₀), g • v₀ = g' • v₀ →
      ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g') • ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩)) := by
    intro g g' hgg' w w' hw hw'
    set h : GL (Fin 2) K₀ := g⁻¹ * g' with hh
    have hhv : h • v₀ = v₀ := by rw [hh, mul_smul, ← hgg', inv_smul_smul]
    have hD := pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq R K₀ K hint hv ϖ₁ h hhv hw'
    have hg' : Matrix.ProjGenLinGroup.mk g' = Matrix.ProjGenLinGroup.mk g * Matrix.ProjGenLinGroup.mk h := by
      rw [← map_mul, hh, mul_inv_cancel_left]
    have hpt : (Matrix.ProjGenLinGroup.mk g') • (⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩ : ↥(upperHalfPlane K₀ K)) =
        (Matrix.ProjGenLinGroup.mk g) • ⟨pmoebius K₀ (Matrix.ProjGenLinGroup.mk h) w', affinoid_subset_upperHalfPlane ϖ₁ 0 hD⟩ := by
      rw [hg', mul_smul]
      rfl
    rw [hpt, ← hFf, ← omegaTranslate_apply P F, ← omegaTranslate_apply P F]
    have hw1 : w ∈ affinoid P 0 := h00 ▸ hw
    have hw2 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk h) w' ∈ affinoid P 0 := h00 ▸ hD
    exact v_apply_eq_of_isUnit P (omegaTranslate P F _) (isUnit_omegaTranslate P hF _) hw1 hw2

  have hchart : ∀ x : LT.LatticeTree.Vertex R K₀, ∃ g : GL (Fin 2) K₀, g • v₀ = x :=
    fun x => LT.LatticeTree.exists_act_stdVertex_eq R K₀ x
  choose gsel hgsel using hchart
  have hback : ∀ x : LT.LatticeTree.Vertex R K₀, (gsel x)⁻¹ • x = v₀ := fun x => inv_smul_eq_iff.mpr (hgsel x).symm

  by_cases hne : ∃ w₀ : K, w₀ ∈ affinoid ϖ₁ 0
  swap
  · have h2 : ∀ (g : GL (Fin 2) K₀)
        (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
        (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
              (∑ e, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * (0 : E → ℤ) e *
                walkCycle (BruhatTits.tree R K₀) (fun e => (eE e).1) p e) :=
      fun g p w w' hw hw' => (hne ⟨w, hw⟩).elim
    exact ⟨0, Submodule.zero_mem _, h2, fun hc => UAP.v_apply_eq_of_current_eq_zero R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex τ eE f hf 0 hc h2⟩
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀P : w₀ ∈ affinoid P 0 := h00 ▸ hw₀

  set val : LT.LatticeTree.Vertex R K₀ → Γ₀ := fun x =>
    Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk (gsel x)) • ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩))
    with hval
  have hvalg : ∀ (x : LT.LatticeTree.Vertex R K₀) (g : GL (Fin 2) K₀), g • v₀ = x → ∀ (w : K) (hw : w ∈ affinoid ϖ₁ 0),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) = val x :=
    fun x g hg w hw => hW g (gsel x) (by rw [hg, hgsel]) w w₀ hw hw₀
  have hval0 : ∀ x, val x ≠ 0 := fun x => hfne _

  have hA : ∀ g : GL (Fin 2) K₀, ∃ m : LT.LatticeTree.Vertex R K₀ → ℤ,
      (∀ S : Finset (LT.LatticeTree.Vertex R K₀), (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj v₀ y) → ∑ y ∈ S, m y = 0) ∧
      ∀ y : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj v₀ y →
        ∀ (g' : GL (Fin 2) K₀), g' • LT.LatticeTree.stdVertex R K₀ = y →
          ∀ (w w' : K) (hw : w ∈ affinoid P 0) (hw' : w' ∈ affinoid P 0),
            Valued.v ((omegaTranslate P F (Matrix.ProjGenLinGroup.mk g) : ↥(upperHalfPlane K₀ K) → K)
                ((Matrix.ProjGenLinGroup.mk g') • ⟨w, affinoid_subset_upperHalfPlane P 0 hw⟩)) =
              Valued.v ((omegaTranslate P F (Matrix.ProjGenLinGroup.mk g) : ↥(upperHalfPlane K₀ K) → K)
                  ⟨w', affinoid_subset_upperHalfPlane P 0 hw'⟩) *
                Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (m y) := fun g =>
    exists_int_neighbours_sum_eq_zero_v_apply_smul_eq R K₀ ϖ hϖ K hint hv hq hrk P hP
      (omegaTranslate P F (Matrix.ProjGenLinGroup.mk g)) (isUnit_omegaTranslate P hF _)
  choose m hmsum hmraw using hA
  have hmstep : ∀ (g : GL (Fin 2) K₀) (y : LT.LatticeTree.Vertex R K₀), (BruhatTits.tree R K₀).Adj v₀ y →
      val (g • y) = val (g • v₀) * q ^ (m g y) := by
    intro g y hy
    have h := hmraw g y hy (gsel y) (hgsel y) w₀ w₀ hw₀P hw₀P
    rw [omegaTranslate_apply, omegaTranslate_apply, ← mul_smul, ← map_mul, hFf] at h
    rw [← hvalg (g • y) (g * gsel y) (by rw [mul_smul, hgsel]) w₀ hw₀, ← hvalg (g • v₀) g rfl w₀ hw₀]
    exact h

  have hone : ∀ a b : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj a b →
      val b = val a * q ^ (m (gsel a) ((gsel a)⁻¹ • b)) := by
    intro a b hab
    have hy : (BruhatTits.tree R K₀).Adj v₀ ((gsel a)⁻¹ • b) := by
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel a)⁻¹ hab
      rwa [hback a] at this
    have := hmstep (gsel a) _ hy
    rwa [smul_inv_smul, hgsel] at this

  have hwalk : ∀ (a b : LT.LatticeTree.Vertex R K₀) (p : (BruhatTits.tree R K₀).Walk a b), ∃ k : ℤ, val a = val b * q ^ k := by
    intro a b p
    induction p with
    | nil => exact ⟨0, by rw [zpow_zero, mul_one]⟩
    | @cons u v w h p ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + m (gsel v) ((gsel v)⁻¹ • u), ?_⟩
      rw [hone v u h.symm, hk, mul_assoc, ← zpow_add₀ hq0.ne']
  have hconn := (CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R K₀).1
  have hex_k : ∀ x : LT.LatticeTree.Vertex R K₀, ∃ k : ℤ, val x = val v₀ * q ^ k :=
    fun x => hwalk x v₀ (hconn.preconnected x v₀).some
  choose φ hφval using hex_k
  have huniq : ∀ (x : LT.LatticeTree.Vertex R K₀) (k : ℤ), val x = val v₀ * q ^ k → k = φ x := by
    intro x k hk
    apply hqinj
    exact mul_left_cancel₀ (hval0 v₀) (hk.symm.trans (hφval x))
  have hφ0 : φ v₀ = 0 := (huniq v₀ 0 (by rw [zpow_zero, mul_one])).symm
  have hdiff : ∀ a b : LT.LatticeTree.Vertex R K₀, (BruhatTits.tree R K₀).Adj a b →
      φ b - φ a = m (gsel a) ((gsel a)⁻¹ • b) := by
    intro a b hab
    have h := hone a b hab
    rw [hφval a, mul_assoc, ← zpow_add₀ hq0.ne'] at h
    have := huniq b _ h
    omega

  have hinvar : ∀ (γ : G) (x : LT.LatticeTree.Vertex R K₀), val (γ • x) = Valued.v ((χ γ : Kˣ) : K) * val x := by
    intro γ x
    obtain ⟨γ', hγ'⟩ := Matrix.ProjGenLinGroup.mk_surjective (ρ γ)
    have hx : γ • x = (γ' * gsel x) • v₀ := by
      rw [hρ, ← hγ', mul_smul, hgsel, BruhatTits.pgl_mk_smul]
    rw [← hvalg (γ • x) (γ' * gsel x) hx.symm w₀ hw₀, ← hvalg x (gsel x) (hgsel x) w₀ hw₀, map_mul, mul_smul, hγ', haut,
      Valuation.map_mul]
  have hφ : ∀ γ : G, ∃ n : ℤ, ∀ x : LT.LatticeTree.Vertex R K₀, φ (γ • x) = φ x + n := by
    intro γ
    refine ⟨φ (γ • v₀), fun x => ?_⟩
    have hχ : Valued.v ((χ γ : Kˣ) : K) = q ^ φ (γ • v₀) := by
      have h := hinvar γ v₀
      rw [hφval (γ • v₀), mul_comm] at h
      exact (mul_right_cancel₀ (hval0 v₀) h).symm
    have h := hinvar γ x
    rw [hχ, hφval x, mul_left_comm, ← zpow_add₀ hq0.ne'] at h
    have := huniq (γ • x) _ h
    omega
  have hharm : ∀ (u : LT.LatticeTree.Vertex R K₀) (S : Finset (LT.LatticeTree.Vertex R K₀)),
      (∀ x, x ∈ S ↔ (BruhatTits.tree R K₀).Adj u x) → ∑ x ∈ S, (φ x - φ u) = 0 := by
    intro u S hS
    rw [Finset.sum_congr rfl (fun x hx => hdiff u x ((hS x).1 hx))]
    rw [← Finset.sum_image (f := fun y => m (gsel u) y) (g := fun x => (gsel u)⁻¹ • x)
      (fun x _ y _ h => smul_left_cancel _ h)]
    refine hmsum (gsel u) _ (fun y => ?_)
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel u)⁻¹ ((hS x).1 hx)
      rwa [hback u] at this
    · intro hy
      refine ⟨gsel u • y, (hS _).2 ?_, inv_smul_smul _ _⟩
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel u) hy
      rwa [hgsel u] at this

  have hnatv : ∀ k : ℕ, Valued.v ((k : ℕ) : K) ≤ 1 := fun k => by
    have : ((k : ℕ) : K) = algebraMap K₀ K (algebraMap R K₀ (k : R)) := by rw [map_natCast, map_natCast]
    rw [this]; exact hint _
  have hdiv : ∀ d : (BruhatTits.tree R K₀).Dart,
      ((Nat.card ↥(stabilizer G d) : ℕ) : ℤ) ∣ φ d.snd - φ d.fst := by
    intro d
    set a := d.fst with hadef
    set b := d.snd with hbdef
    have hab : (BruhatTits.tree R K₀).Adj a b := d.adj
    rw [hdiff a b hab]
    set ga : GL (Fin 2) K₀ := gsel a with hga
    set gP : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk ga with hgP
    set y : LT.LatticeTree.Vertex R K₀ := ga⁻¹ • b with hydef
    have hy : (BruhatTits.tree R K₀).Adj v₀ y := by
      have := GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (gsel a)⁻¹ hab
      rwa [hback a] at this

    let φa : G →* PGL(2, K₀) := (MulAut.conj gP⁻¹).toMonoidHom.comp ρ
    have hφa : ∀ σ : G, φa σ = gP⁻¹ * ρ σ * gP := fun σ => by
      show gP⁻¹ * ρ σ * (gP⁻¹)⁻¹ = _; rw [inv_inv]
    have hφinj : Function.Injective φa := (MulAut.conj gP⁻¹).injective.comp hρinj
    haveI hfinSd : Finite ↥(stabilizer G d) :=
      Finite.of_injective (Subgroup.inclusion (stabilizer_dart_le (BruhatTits.tree R K₀) d))
        (Subgroup.inclusion_injective _)
    set H : Subgroup PGL(2, K₀) := (stabilizer G d).map φa with hHdef
    haveI hfinH : Finite ↥H :=
      Finite.of_surjective (fun s : ↥(stabilizer G d) => (⟨φa s, Subgroup.mem_map_of_mem φa s.2⟩ : ↥H)) (by
        rintro ⟨h, hh⟩
        obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hh
        exact ⟨⟨s, hs⟩, rfl⟩)
    have hcard : Nat.card ↥H = Nat.card ↥(stabilizer G d) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (stabilizer G d) φa hφinj).toEquiv).symm

    have hgPv₀ : gP • v₀ = a := by rw [hgP, BruhatTits.pgl_mk_smul, hga, hgsel]
    have hgPy : gP • y = b := by rw [hgP, BruhatTits.pgl_mk_smul, hydef, hga, smul_inv_smul]
    have hstab : ∀ σ ∈ stabilizer G d, σ • a = a ∧ σ • b = b := fun σ hσ => by
      have := MulAction.mem_stabilizer_iff.1 hσ
      exact ⟨by rw [hadef, ← smul_dart_fst, this], by rw [hbdef, ← smul_dart_snd, this]⟩
    have hH0 : ∀ h ∈ H, h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀ := by
      intro h hh
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hh
      rw [hφa, mul_smul, mul_smul, show (v₀ : LT.LatticeTree.Vertex R K₀) = LT.LatticeTree.stdVertex R K₀ from rfl] at *
      rw [hgPv₀, ← hρ, (hstab σ hσ).1, ← hgPv₀, inv_smul_smul]
    have hHy : ∀ h ∈ H, h • y = y := by
      intro h hh
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hh
      rw [hφa, mul_smul, mul_smul, hgPy, ← hρ, (hstab σ hσ).2, ← hgPy, inv_smul_smul]

    have htameH : Valued.v ((Nat.card ↥H : ℕ) : K) = 1 := by
      rw [hcard]
      have hdvd : Nat.card ↥(stabilizer G d) ∣ Nat.card ↥(stabilizer G a) :=
        Subgroup.card_dvd_of_le (stabilizer_dart_le (BruhatTits.tree R K₀) d)
      obtain ⟨k, hk⟩ := hdvd
      have h1 := htame a
      rw [hk, Nat.cast_mul, map_mul] at h1
      exact le_antisymm (hnatv _) (by
        calc (1 : Γ₀) = Valued.v ((Nat.card ↥(stabilizer G d) : ℕ) : K) * Valued.v ((k : ℕ) : K) := h1.symm
          _ ≤ Valued.v ((Nat.card ↥(stabilizer G d) : ℕ) : K) * 1 := mul_le_mul_right (hnatv k) _
          _ = _ := mul_one _)

    have hinvF : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K),
        (omegaTranslate P F gP : ↥(upperHalfPlane K₀ K) → K) (h • z) =
          (omegaTranslate P F gP : ↥(upperHalfPlane K₀ K) → K) z := by
      intro h hh z
      obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hh
      have hfo : IsOfFinOrder σ := by
        have := isOfFinOrder_of_finite (⟨σ, hσ⟩ : ↥(stabilizer G d))
        exact (stabilizer G d).subtype.isOfFinOrder this
      have hχσ : ((χ σ : Kˣ) : K) = 1 := by rw [hχ σ hfo, Units.val_one]
      rw [omegaTranslate_apply, omegaTranslate_apply, hφa, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel,
        one_mul, mul_smul, hFf, haut, hχσ, one_mul]
    have key := CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq R K₀ ϖ hϖ K hint hv hq
      hrk P hP (omegaTranslate P F gP) (isUnit_omegaTranslate P hF gP) y hy H hH0 hHy htameH hinvF (m ga y)
      (hmraw ga y hy)
    rwa [hcard] at key

  obtain ⟨c, hcdef, hmem, hcycle⟩ :=
    CerednikDrinfeld.Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
      (BruhatTits.tree R K₀) hfin τ hτ hadj
      (⟨fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
        fun e => Quotient.mk (orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd,
        fun _ => 1⟩ : DegeneracyData E (QuotVert G (LT.LatticeTree.Vertex R K₀)))
      eE (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) φ hφ hharm hdiv
  have h2 : ∀ (g : GL (Fin 2) K₀)
      (p : (BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀))
      (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
        Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
            (∑ e, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) * c e *
                walkCycle (BruhatTits.tree R K₀) (fun e => (eE e).1) p e) := by
    intro g p w w' hw hw'
    have hg := hvalg (g • v₀) g rfl w hw
    have h1 : Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) = val v₀ := by
      have := hvalg v₀ 1 (one_smul _ _) w' hw'
      rwa [map_one, one_smul] at this
    have hk := hcycle v₀ (g • v₀) p
    rw [hφ0, sub_zero] at hk
    rw [hg, h1, hφval (g • v₀), hk]
  refine ⟨c, hmem, h2, fun hcz => ?_⟩
  refine UAP.v_apply_eq_of_current_eq_zero R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex τ eE f hf 0 rfl fun g p w w' hw hw' => ?_
  have := h2 g p w w' hw hw'
  simp only [hcz, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] at this ⊢
  exact this

end S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder (solution)
