-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/fe937c61-87c7-53d8-b22a-ddec3dabaf87

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.injEq CerednikDrinfeld.SpecialFormal.ModuliPackage.G_map CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.mk.sizeOf_spec CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.map_ψ CerednikDrinfeld.SpecialFormal.ModuliPackage.G_obj"

set_option autoImplicit false

open scoped Matrix

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open LT.LatticeTree in

theorem C1oneAux.eq_of_le_of_hasDetIndex
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (N N' : Submodule 𝒪 (Fin 2 → K)) (e : ℤ)
    (h : FormalOmega.HasDetIndex π N e) (h' : FormalOmega.HasDetIndex π N' e) (hle : N ≤ N') : N = N' := by
  classical
  obtain ⟨g, hg, u, hu⟩ := h
  obtain ⟨g', hg', u', hu'⟩ := h'
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K

  set h₀ : Matrix.GeneralLinearGroup (Fin 2) K := g'⁻¹ * g with hh₀
  have hstd : latticeMap h₀ (stdLattice 𝒪 K) ≤ stdLattice 𝒪 K := by
    have : latticeMap g (stdLattice 𝒪 K) ≤ latticeMap g' (stdLattice 𝒪 K) := by rw [hg, hg']; exact hle
    have := latticeMap_mono g'⁻¹ this
    rwa [latticeMap_inv_latticeMap, ← latticeMap_mul] at this
  have hcol : ∀ i j, IsLocalization.IsInteger 𝒪 ((h₀ : Matrix (Fin 2) (Fin 2) K) i j) := by
    intro i j
    have hj : (h₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ (Pi.single j 1) ∈ stdLattice 𝒪 K :=
      hstd (mulVec_mem_latticeMap (single_one_mem_stdLattice 𝒪 K j))
    have := hj i
    rwa [mulVec_single_one] at this
  choose a ha using fun q : Fin 2 × Fin 2 => hcol q.1 q.2
  set A : Matrix (Fin 2) (Fin 2) 𝒪 := Matrix.of fun i j => a (i, j) with hA
  have hmapA : (algebraMap 𝒪 K).mapMatrix A = (h₀ : Matrix (Fin 2) (Fin 2) K) := by
    ext i j; exact ha (i, j)

  have hπe : algebraMap 𝒪 K π ^ e ≠ 0 := by
    intro h0
    have : ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = 0 := by rw [hu, h0, mul_zero]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero this
  have hdet : ((Matrix.GeneralLinearGroup.det h₀ : Kˣ) : K) = algebraMap 𝒪 K u * (algebraMap 𝒪 K u')⁻¹ := by
    rw [hh₀, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hu, hu']
    have hu'0 : algebraMap 𝒪 K u' ≠ 0 := by
      intro h0; exact hinj.ne u'.ne_zero (by rw [h0, map_zero])
    field_simp
  have hdetA : algebraMap 𝒪 K A.det = algebraMap 𝒪 K u * (algebraMap 𝒪 K u')⁻¹ := by
    rw [← hdet, Matrix.GeneralLinearGroup.val_det_apply, ← hmapA]
    exact RingHom.map_det (algebraMap 𝒪 K) A
  have hdetA' : A.det * (u' : 𝒪) = u := by
    apply hinj
    have hu'0 : algebraMap 𝒪 K u' ≠ 0 := by
      intro h0; exact hinj.ne u'.ne_zero (by rw [h0, map_zero])
    rw [map_mul, hdetA]; field_simp
  have hunit : IsUnit A.det := by
    have : IsUnit (A.det * (u' : 𝒪)) := by rw [hdetA']; exact Units.isUnit u
    exact isUnit_of_mul_isUnit_left this

  have hmem : h₀ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap 𝒪 K)).range := by
    refine ⟨Matrix.GeneralLinearGroup.mk'' A hunit, ?_⟩
    ext i j
    exact ha (i, j)
  have hfix : latticeMap h₀ (stdLattice 𝒪 K) = stdLattice 𝒪 K := (latticeMap_stdLattice_eq_iff_mem_range h₀).mpr hmem
  rw [← hg, ← hg', show g = g' * h₀ by rw [hh₀, mul_inv_cancel_left], latticeMap_mul, hfix]

open LT.LatticeTree in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) :
    ∀ x : PrimeSpectrum B,
      Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
      ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieZero (structureMap ι ψ) →
          N₁ y = N₁ x := by
  classical
  intro x hx
  obtain ⟨g, hg, u, hu⟩ := CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
    p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₁ hN₁ x hx

  have hgen : ∀ j : Fin 2, (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) *ᵥ (Pi.single j 1) ∈ N₁ x := fun j =>
    hg ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice ℤ_[p] ℚ_[p] j)
  choose f hf using fun j => (hN₁ x _).mp (hgen j)
  refine ⟨{y | ∀ j : Fin 2, f j ∉ y.asIdeal}, ?_, fun j => (hf j).1, ?_⟩
  · have : {y : PrimeSpectrum B | ∀ j : Fin 2, f j ∉ y.asIdeal} = ⋂ j : Fin 2, (PrimeSpectrum.basicOpen (f j) : Set (PrimeSpectrum B)) := by
      ext y; simp [PrimeSpectrum.mem_basicOpen]
    rw [this]
    exact isOpen_iInter_of_finite fun j => (PrimeSpectrum.basicOpen (f j)).isOpen
  · intro y hy hyS

    have hle : N₁ x ≤ N₁ y := by
      rw [← hg, latticeMap, stdLattice_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      rw [mulVecLinR_apply]
      exact (hN₁ y _).mpr ⟨f j, hy j, (hf j).2⟩
    have hy0 := CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
      p k ι Φ hΦ hΦ4 h0Φ hcΦ rΦ hLΦ hrΦ ψ hB t ht N₁ hN₁ y hyS
    exact (C1oneAux.eq_of_le_of_hasDetIndex (p : ℤ_[p]) (N₁ x) (N₁ y) (-1) ⟨g, hg, u, hu⟩ hy0 hle).symm

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector (solution)
