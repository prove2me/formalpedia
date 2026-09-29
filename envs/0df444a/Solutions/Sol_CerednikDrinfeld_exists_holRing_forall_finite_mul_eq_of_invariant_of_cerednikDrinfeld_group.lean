-- Prove2me | solution 1 for CerednikDrinfeld.exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4f94a623-1560-5982-b34d-0ed2ef1681bb

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
import Theorems.Thm_CerednikDrinfeld_map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group
p2m_attr_erase "instance" "AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    {C : Type} [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    [CompleteSpace C] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : C, y ≠ 0 ∧ Valued.v y ≤ ε)
    (hex : Omega.IsExhausted ϖ) [IsDomain (Omega.HolRingOf ϖ ρ)]

    (F : ↥(Omega.upperHalfPlane K₀ C) → C)
    (hinv : ∀ (γ : G), γ ∈ Γ' → ∀ z w : ↥(Omega.upperHalfPlane K₀ C),
      (w : C) = Omega.pmoebius K₀ (ρ γ) (z : C) → F w = F z)
    (hmer : ∀ n : ℕ, ∃ a b : ↥(Omega.affinoid ϖ n) → C, a ∈ Omega.holOn C (Omega.affinoid ϖ n) ∧ b ∈ Omega.holOn C (Omega.affinoid ϖ n) ∧
      (∃ z : ↥(Omega.affinoid ϖ n), b z ≠ 0) ∧
      ∀ z : ↥(Omega.affinoid ϖ n), b z ≠ 0 →
        b z * F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ = a z) :
    ∃ Φ H : ↥(Omega.holRing ϖ), H ≠ 0 ∧
      ∀ n : ℕ, ∃ Z : Set ↥(Omega.affinoid ϖ n), Z.Finite ∧
        ∀ z : ↥(Omega.affinoid ϖ n), z ∉ Z →
          (H : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ *
              F ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ =
            (Φ : ↥(Omega.upperHalfPlane K₀ C) → C) ⟨(z : C), Omega.affinoid_subset_upperHalfPlane ϖ n z.2⟩ := by
  classical
  haveI : IsDiscreteValuationRing 𝒪 := hdvr

  obtain ⟨hTP, hGA, -, hQV, -⟩ :=
    CerednikDrinfeld.map_evenPart_le_typePreserving_and_graphAction_and_finite_of_cerednikDrinfeld_group
      𝒪 hdvr π hπ hcomplete hres hunr K₀ vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt
  haveI : Mumford.GraphAction ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀) := hGA
  haveI : Finite (Mumford.QuotVert ↥(Γ'.map ρ) (LT.LatticeTree.Vertex 𝒪 K₀)) := hQV

  haveI : Finite (𝒪 ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)

  haveI : IsDomain ↥(Omega.holRing ϖ) := (Omega.HolRingOf.isDomain_iff ϖ ρ).1 inferInstance

  obtain ⟨hconn, hcol⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two 𝒪 K₀
  obtain ⟨hadj₁, -, -⟩ :=
    CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
      ↥(Γ'.map ρ) (BruhatTits.tree 𝒪 K₀) hconn hcol (LT.LatticeTree.stdVertex 𝒪 K₀)

  have hπC : algebraMap K₀ C (algebraMap 𝒪 K₀ π) = algebraMap K₀ C ϖ.ϖ := by
    rw [← IsScalarTower.algebraMap_apply 𝒪 K₀ C π]; exact hF.unif
  refine CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
    𝒪 K₀ π hπ C ?_ ?_ ?_ hrk ϖ hex (Γ'.map ρ).subtype ?_ ?_
    (Mumford.vertexType (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀)) ?_ ?_ F ?_ hmer
  ·
    intro a
    exact (hF.integers (algebraMap 𝒪 K₀ a)).2 ⟨a, rfl⟩
  ·
    intro a ha
    obtain ⟨x, hx⟩ := (hF.integers a).1 ha
    exact RingHom.mem_rangeS.mpr ⟨x, hx⟩
  ·
    intro ε hε
    obtain ⟨y, hy0, hyε⟩ := hval ε hε
    obtain ⟨n, hn⟩ := hrk (algebraMap K₀ C ϖ.ϖ) y ϖ.lt_one hy0
    exact ⟨n, by rw [hπC]; exact hn.trans hyε⟩
  ·
    intro g w
    rfl
  ·
    intro w
    haveI := (hdisc w).to_subtype
    refine Finite.of_injective
      (fun x : ↥(MulAction.stabilizer (↥(Γ'.map ρ)) w) =>
        (⟨((x : ↥(Γ'.map ρ)) : PGL(2, K₀)), (x : ↥(Γ'.map ρ)).2, MulAction.mem_stabilizer_iff.1 x.2⟩ :
          ↥{g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • w = w})) ?_
    intro a b h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  ·
    intro g w
    exact (Mumford.mem_typePreserving_iff _ _ _).1 (hTP g.2) w
  ·
    intro u w huw
    rw [hadj₁ u w huw]
    simp
  ·
    intro γ z w h
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 γ.2
    exact hinv x hx z w (by rw [hxe]; exact h)

end S_CerednikDrinfeld_exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group
end P2MW
export P2MW.S_CerednikDrinfeld_exists_holRing_forall_finite_mul_eq_of_invariant_of_cerednikDrinfeld_group (solution)
