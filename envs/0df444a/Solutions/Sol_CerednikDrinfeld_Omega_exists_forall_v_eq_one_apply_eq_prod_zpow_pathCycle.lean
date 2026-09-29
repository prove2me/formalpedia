-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/bea006ac-775e-5040-9bea-8409e2ad5cc8

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_Ribbon
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CycleUnitCoords

def unitSphere (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] : Subgroup Kˣ where
  carrier := {x | Valued.v ((x : Kˣ) : K) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at hx hy ⊢
    rw [hx, hy, one_mul]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
    rw [hx, inv_one]

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem mem_unitSphere (x : Kˣ) : x ∈ unitSphere K ↔ Valued.v ((x : Kˣ) : K) = 1 := Iff.rfl

theorem exists_pow_eq [IsAlgClosed K] (u : ↥(unitSphere K)) (n : ℕ) (hn : 0 < n) :
    ∃ x : ↥(unitSphere K), x ^ n = u := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (((u : ↥(unitSphere K)) : Kˣ) : K) hn
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, zero_pow hn.ne'] at hy; exact ((u : ↥(unitSphere K)) : Kˣ).ne_zero hy.symm
  have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hvy : Valued.v y = 1 := by
    have h := congrArg Valued.v hy
    rw [map_pow, (mem_unitSphere _).1 u.2] at h
    have hu : (Units.mk0 (Valued.v y) hvy0) ^ n = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact h
    have := (pow_eq_one_iff.1 hu).resolve_right hn.ne'
    exact (Units.val_mk0 hvy0).symm.trans (congrArg Units.val this)
  refine ⟨⟨Units.mk0 y hy0, by rw [mem_unitSphere, Units.val_mk0]; exact hvy⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  simp [hy]

theorem exists_zsmul_eq [IsAlgClosed K] (a : Additive ↥(unitSphere K)) (n : ℤ) (hn : n ≠ 0) :
    ∃ b : Additive ↥(unitSphere K), n • b = a := by
  obtain ⟨y, hy⟩ := exists_pow_eq (Additive.toMul a) n.natAbs (Int.natAbs_pos.2 hn)
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨Additive.ofMul y⁻¹, ?_⟩
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul, inv_zpow', ← hy, ← zpow_natCast]
    congr 1
    omega
  · refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul, ← hy, ← zpow_natCast]
    congr 1
    omega

noncomputable scoped instance instDivisibleBy [IsAlgClosed K] : DivisibleBy (Additive ↥(unitSphere K)) ℤ where
  div a n := if hn : n = 0 then 0 else (exists_zsmul_eq a n hn).choose
  div_zero a := dif_pos rfl
  div_cancel a hn := by
    show _ • (dite _ _ _) = a
    rw [dif_neg hn]
    exact (exists_zsmul_eq a _ hn).choose_spec

end CycleUnitCoords
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle.CycleUnitCoords"

open CycleUnitCoords in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀]
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    {G : Type} [Group G]
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})

    (η : G →* Kˣ) (hη₁ : ∀ β : G, Valued.v ((η β : Kˣ) : K) = 1) (hη : ∀ γ : G, IsOfFinOrder γ → η γ = 1) :
    ∃ ζ : E → Kˣ, (∀ e : E, Valued.v ((ζ e : Kˣ) : K) = 1) ∧
      ∀ β : G, ((η β : Kˣ) : K) = ∏ e : E, ((ζ e : Kˣ) : K) ^
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) β e := by
  classical
  have hT := CerednikDrinfeld.BruhatTits.tree_isTree R K₀
  let V := CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀)
  let D : CerednikDrinfeld.DegeneracyData E V :=
    ⟨fun e => Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.fst,
     fun e => Quotient.mk (MulAction.orbitRel G (LT.LatticeTree.Vertex R K₀)) (eE e).1.out.snd, fun _ => 1⟩
  obtain ⟨Φ, hΦ⟩ := CerednikDrinfeld.Mumford.exists_addMonoidHom_abelianization_ribbonKernel_apply_eq_pathCycle
    (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl V) (fun _ => rfl) (fun _ => rfl)
    (LT.LatticeTree.stdVertex R K₀)
  have hdiv : ∀ (a : ↥(unitSphere K)) (n : ℕ), n ≠ 0 → ∃ b : ↥(unitSphere K), b ^ n = a :=
    fun a n hn => exists_pow_eq a n (Nat.pos_of_ne_zero hn)
  have hηU : ∀ g : G, η g ∈ unitSphere K := fun g => hη₁ g
  let c : G →* ↥(unitSphere K) := η.codRestrict (unitSphere K) hηU
  have hc : ∀ (w : LT.LatticeTree.Vertex R K₀) (g : G), g ∈ MulAction.stabilizer G w → c g = 1 := by
    intro w g hg
    haveI := hfin w
    have hfo : IsOfFinOrder g :=
      (MulAction.stabilizer G w).subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨g, hg⟩ : ↥(MulAction.stabilizer G w)))
    apply Subtype.ext
    show ((η g : Kˣ)) = ((1 : ↥(unitSphere K)) : Kˣ)
    rw [hη g hfo, OneMemClass.coe_one]
  obtain ⟨ν, hν⟩ := CerednikDrinfeld.Mumford.exists_eq_prod_pow_of_forall_mem_stabilizer_of_forall_exists_pow_eq
    (CerednikDrinfeld.BruhatTits.tree R K₀) hT τ hτ hadj D eE (Equiv.refl V) (fun _ => rfl) (fun _ => rfl)
    (LT.LatticeTree.stdVertex R K₀) Φ hΦ ↥(unitSphere K) hdiv c hc
  refine ⟨fun e => ((ν e : ↥(unitSphere K)) : Kˣ), fun e => (ν e).2, fun β => ?_⟩
  have h := hν β
  rw [hΦ β] at h
  have h2 := congrArg (fun u : ↥(unitSphere K) => ((u : Kˣ) : K)) h
  simp only [Subgroup.val_finset_prod, SubgroupClass.coe_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val] at h2
  exact h2

end S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_v_eq_one_apply_eq_prod_zpow_pathCycle (solution)
