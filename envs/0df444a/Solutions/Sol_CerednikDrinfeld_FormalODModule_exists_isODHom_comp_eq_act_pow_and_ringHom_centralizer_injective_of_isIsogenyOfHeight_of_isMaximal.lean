-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_and_ringHom_centralizer_injective_of_isIsogenyOfHeight_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/00eeb34b-d714-5181-8c17-012f95b9f96f

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_and_ringHom_centralizer_injective_of_isIsogenyOfHeight_of_isMaximal
p2m_attr_erase "instance" "CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.Scheme.nilpPoints_map_val LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq"
p2m_attr_erase "simp" "CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀]
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)) (hΦ4 : Φ.HasHeight 4)
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))
    (E₀ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀) :
    ∃ (N₀ : ℕ) (β₀' : Series (Onr ⧸ pIdeal r Onr))
      (E_X : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀),
      FormalODModule.IsODHom (X₀.map κ) Φ β₀' ∧ β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ N₀) ∧
      β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N₀) ∧ Function.Injective E_X ∧
      ∀ ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
        ∃ e : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
          (e : MvFormalGroup.End Φ.F).toPowerSeries =
            β₀'.comp ((Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
          E₀ e = ((r : K₀) ^ N₀) • E_X ε := by
  classical

  have hpr : pIdeal r Onr = Ideal.span {algebraMap 𝒪 Onr π} := by
    have h1 : Ideal.map (algebraMap 𝒪 Onr) (Ideal.span {((r : ℕ) : 𝒪)}) = Ideal.map (algebraMap 𝒪 Onr) (Ideal.span {π}) := by
      rw [hunr]
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast] at h1
    exact h1
  haveI hmax : (pIdeal r Onr).IsMaximal := by rw [hpr]; exact hOnr_max
  letI instF : Field (Onr ⧸ pIdeal r Onr) := Ideal.Quotient.field (pIdeal r Onr)

  have hB : IsNilpotent ((r : ℕ) : Onr ⧸ pIdeal r Onr) := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal r Onr)), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  obtain ⟨N₀, β₀', hβ₀', h₁⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isODHom_comp_eq_act_pow_of_isIsogenyOfHeight_of_field r hB Φ (X₀.map κ) β₀
      (4 * n₀) hβ₀
  have hβ00 : ∀ i, MvPowerSeries.constantCoeff (β₀ i) = 0 := hβ₀.1.constantCoeff
  have hβ0'0 : ∀ i, MvPowerSeries.constantCoeff (β₀' i) = 0 := hβ₀'.constantCoeff

  have hc₁ : ∀ σ τ : Series (Onr ⧸ pIdeal r Onr), σ.comp β₀ = τ.comp β₀ → σ = τ := by
    intro σ τ h
    funext i
    exact CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree β₀ hβ00 hβ₀.2 (σ i) (τ i) (congrFun h i)

  have h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N₀) := by
    apply hc₁
    rw [Series.comp_assoc _ _ _ hβ0'0 hβ00, h₁, hβ₀.1.2.1]

  have hcr : ∀ σ τ : Series (Onr ⧸ pIdeal r Onr), σ.comp (Φ.act (r : Zp2 r)) = τ.comp (Φ.act (r : Zp2 r)) → σ = τ := by
    intro σ τ h
    funext i
    exact CerednikDrinfeld.FormalODModule.subst_injective_of_hasKernelOfDegree (Φ.act (r : Zp2 r)) (Φ.isLawHom_act _).1
      hΦ4 (σ i) (τ i) (congrFun h i)
  have hc₂ : ∀ (n : ℕ) (σ τ : Series (Onr ⧸ pIdeal r Onr)),
      σ.comp (Φ.act ((r : Zp2 r) ^ n)) = τ.comp (Φ.act ((r : Zp2 r) ^ n)) → σ = τ := by
    intro n
    induction n with
    | zero =>
      intro σ τ h
      simpa only [pow_zero, Φ.act_one, Series.comp_id] using h
    | succ n ih =>
      intro σ τ h
      rw [pow_succ, Φ.act_mul, ← Series.comp_assoc _ _ _ (Φ.isLawHom_act _).1 (Φ.isLawHom_act _).1,
        ← Series.comp_assoc _ _ _ (Φ.isLawHom_act _).1 (Φ.isLawHom_act _).1] at h
      exact ih σ τ (hcr _ _ h)

  have hκinj : Function.Injective κ := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := RingHom.congr_fun hκ x
    have hy := RingHom.congr_fun hκ y
    simp only [RingHom.coe_comp, Function.comp_apply] at hx hy
    rw [hx, hy, Ideal.Quotient.eq, hpr] at hxy
    exact (Ideal.Quotient.eq).mpr hxy
  obtain ⟨E_X, hinj, hAd⟩ :=
    CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
      κ hκinj X₀ Φ β₀ β₀' N₀ hβ₀.1 hβ₀' h₁ h₂ hc₁ (hc₂ N₀) E₀ hE₀
  exact ⟨N₀, β₀', E_X, hβ₀', h₁, h₂, hinj, hAd⟩

end S_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_and_ringHom_centralizer_injective_of_isIsogenyOfHeight_of_isMaximal
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_comp_eq_act_pow_and_ringHom_centralizer_injective_of_isIsogenyOfHeight_of_isMaximal (solution)
