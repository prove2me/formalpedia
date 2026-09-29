-- Prove2me | solution 1 for CerednikDrinfeld.exists_formalQuotientDatum_coeff_adicFib
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b7f178a6-caa4-50e2-b31c-7c09bb7e3b02

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even
import Theorems.Thm_CerednikDrinfeld_BruhatTits_treeLattice_facts_map_evenPart
import Theorems.Thm_CerednikDrinfeld_FormalOmega_nonempty_mumfordTower_of_isSchottky
import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_exists_twistedTower
import Theorems.Thm_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat
import Theorems.Thm_CerednikDrinfeld_exists_formalQuotientDatum_coeff_adicFib_of_mumfordTower_of_towerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_formalQuotientDatum_coeff_adicFib
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀ AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
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

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    :
    ∃ D : FormalQuotientDatum 𝒪 π K₀ Onr Fr vdet r σ Γ Γ' g₁,

      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (ψ ψ' : Onr →ₐ[𝒪] B) (P : (Omega K₀ π).obj B),
          (∀ y : Onr, Fr (Fr y) = y → ψ y = ψ' y) → D.q n B hB (ψ, P) = D.q n B hB (ψ', P)) ∧

      (∀ (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] (Γ₀ : Type) [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
          [CompleteSpace C] [IsAlgClosed C]
          (R : Type) [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
          (ϖ : PseudoUniformizer K₀ C), IsAdicFrame π ϖ R → ∀ (ψ₀ : Onr →ₐ[𝒪] R)
          (hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0),
        (∀ η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ D.Y n,
          (∀ n : ℕ, η n ≫ D.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
            Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n)))) →
          (∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ D.yt n) →
          ∃ x : AdicPoint K₀ π R, ∀ n : ℕ, η n = D.q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n)) ∧
        (∀ x x' : AdicPoint K₀ π R,
          (∀ n : ℕ, D.q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) = D.q n (modPow π R n) (hmod n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n)) ↔
          ∃ γ ∈ Γ, ∀ n : ℕ, OmegaNr.IsTwistedAct π Onr Fr vdet (modPow π R n) (σ γ) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x.pt n) (((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)})).comp ψ₀), x'.pt n))) := by
  classical
  have hF0 : ∃ N : Subgroup (PGL(2, K₀)), N ≤ Γ'.map ρ ∧ (N.subgroupOf (Γ.map ρ)).Normal ∧ N.relIndex (Γ'.map ρ) ≠ 0 ∧
      Mumford.IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀) :=
    CerednikDrinfeld.exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even 𝒪 hdvr π hπ hres K₀ vdet hvdet G σ Γ Γ' hΓ' ρ hρ hdisc hcocpt
  obtain ⟨N, hNle, hNnorm, hNidx, hNsch⟩ := hF0
  have hfacts : (∀ w : LT.LatticeTree.Vertex 𝒪 K₀, Finite (MulAction.stabilizer (↥(Γ'.map ρ)) w)) ∧
      Finite (Mumford.QuotVert (↥(Γ'.map ρ)) (LT.LatticeTree.Vertex 𝒪 K₀)) ∧
      Finite (Mumford.QuotEdge (↥(Γ'.map ρ)) (BruhatTits.tree 𝒪 K₀)) ∧
      Γ'.map ρ ≤ Mumford.typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) ∧
      (∀ g ∈ Γ'.map ρ, ∀ d : (BruhatTits.tree 𝒪 K₀).Dart, g • d ≠ d.symm) ∧
      (Γ'.map ρ).FG ∧ (Γ'.map ρ).relIndex (Γ.map ρ) ≠ 0 :=
    CerednikDrinfeld.BruhatTits.treeLattice_facts_map_evenPart 𝒪 hdvr π hπ hres K₀ vdet hvdet G σ Γ Γ' hΓ' ρ hρ hdisc hcocpt
  have hNtype : N ≤ Mumford.typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀) :=
    hNle.trans hfacts.2.2.2.1
  have hDM : Nonempty (MumfordTower 𝒪 π K₀ r g₁ N) :=
    CerednikDrinfeld.FormalOmega.nonempty_mumfordTower_of_isSchottky 𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hNsch hNtype
  obtain ⟨DM⟩ := hDM
  obtain ⟨X, xb, xt, G₂, instG, instF, a, pr₁, pr₂, θ, Fr₂, hcart, hproper, hflat, haff, ha_over, ha_xt, hX, hxb, hxt₁, hxt₂, hθsurj,
      hθker, hFr₂, ha_pr₂, ha_pr₁⟩ :=
    CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg
      hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁ N hNle hNnorm hNidx DM
  have hDQ : Nonempty (TowerQuotientDatum 𝒪 π X xb xt G₂ a) :=
    AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G₂ a ha_over ha_xt
  obtain ⟨DQ⟩ := hDQ
  exact CerednikDrinfeld.exists_formalQuotientDatum_coeff_adicFib_of_mumfordTower_of_towerQuotientDatum 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
    hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁ N hNle hNnorm hNidx DM X xb xt G₂
    a pr₁ pr₂ θ Fr₂ hcart hproper hflat haff ha_over ha_xt hX hxb hxt₁ hxt₂ hθsurj hθker hFr₂ ha_pr₂ ha_pr₁ DQ

end S_CerednikDrinfeld_exists_formalQuotientDatum_coeff_adicFib
end P2MW
export P2MW.S_CerednikDrinfeld_exists_formalQuotientDatum_coeff_adicFib (solution)
