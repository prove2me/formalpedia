-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fb4b1bc9-95b5-5c7a-94e3-a2bb32f7ef44

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber
p2m_attr_erase "instance" "CerednikDrinfeld.BruhatTits.instGraphActionGLTree CerednikDrinfeld.BruhatTits.instMulActionGLVertex CerednikDrinfeld.BruhatTits.instGraphActionPGLTree CerednikDrinfeld.BruhatTits.instMulActionPGLVertex CerednikDrinfeld.Mumford.dartAction CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀ CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply CerednikDrinfeld.BruhatTits.vertPermHom_apply CerednikDrinfeld.BruhatTits.gl_smul_mk CerednikDrinfeld.BruhatTits.pgl_mk_smul CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

namespace K1LatticePlane

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

theorem smul_row_injective {n : Type} [Fintype n] [DecidableEq n]
    (T : Matrix n n B) (hT : IsUnit T.det)
    (i : n) (x y : B) (h : x • T i = y • T i) : x = y := by
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  obtain ⟨u, hu⟩ := hTu
  have key : ∀ v : n → B, Matrix.vecMul (Matrix.vecMul v T) (↑u⁻¹ : Matrix n n B) = v := by
    intro v
    rw [Matrix.vecMul_vecMul, ← hu, Units.mul_inv, Matrix.vecMul_one]
  have hrow : ∀ w : B, Matrix.vecMul (Pi.single i w) T = w • T i := by
    intro w
    rw [Matrix.single_vecMul]
    rfl
  have h1 : Matrix.vecMul (Pi.single i x) T = Matrix.vecMul (Pi.single i y) T := by
    rw [hrow, hrow, h]
  have h2 : (Pi.single i x : n → B) = Pi.single i y := by
    rw [← key (Pi.single i x), h1, key]
  have h3 := congrFun h2 i
  rwa [Pi.single_eq_same, Pi.single_eq_same] at h3

theorem tangent_sum_homothety {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm]
    {ι : Type} [Fintype ι] (c : ι → B) (e : ι → CartierModule p Φ) :
    tangent (∑ i, homothety (c i) (e i)) = Matrix.vecMul c (Matrix.of fun i k => tangent (e i) k) := by
  rw [map_sum]
  funext k
  simp only [Finset.sum_apply, tangent_homothety, Pi.smul_apply, smul_eq_mul, Matrix.vecMul,
    Matrix.of_apply]
  rfl

theorem exists_eq_homothety_add_verschiebungInt (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hker : ∀ f : CartierModule p X.F, tangent f = 0 ↔ ∃ g : CartierModule p X.F, verschiebungInt g = f)
    (i₀ : Fin 2) (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i₀ : ℕ)) :
    ∃ (c : B) (y : CartierModule p X.F), y ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ) ∧
      m = homothety c (γ i₀) + verschiebungInt y := by
  classical
  have h10 : i₀ + 1 + 1 = i₀ := by fin_cases i₀ <;> rfl
  have hhom : ∀ (a : B) (n : ℕ) (f : CartierModule p X.F), f ∈ X.gradedPiece j n →
      homothety a f ∈ X.gradedPiece j n := fun a n f hf => by
    rw [← teichmuller_smul]; exact FormalODModule.smul_mem_gradedPiece X j n _ f hf
  have hV1 : ∀ (i : Fin 2) (f : CartierModule p X.F), f ∈ X.gradedPiece j (i : ℕ) →
      verschiebungInt f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ) :=
    fun i f hf => (X.toGradedCartierModuleData j hc).verschiebung_mem i f hf
  have hdisj : ∀ q : CartierModule p X.F, q ∈ X.gradedPiece j (i₀ : ℕ) →
      q ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ) → q = 0 := by
    intro q h1 h2
    have hq : q ∈ X.gradedPiece j 0 ⊓ X.gradedPiece j 1 := by
      fin_cases i₀
      · exact AddSubgroup.mem_inf.2 ⟨h1, h2⟩
      · exact AddSubgroup.mem_inf.2 ⟨h2, h1⟩
    rwa [hc.inf_eq_bot, AddSubgroup.mem_bot] at hq
  have hsum : ∀ f : Fin 2 → CartierModule p X.F, ∑ i, f i = f i₀ + f (i₀ + 1) := by
    intro f
    fin_cases i₀
    · simp [Fin.sum_univ_two]
    · simp [Fin.sum_univ_two, add_comm]
  set T : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i k => tangent (γ i) k with hT
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det T).mpr hγ.2
  set c : Fin 2 → B := Matrix.vecMul (tangent m) (↑u⁻¹ : Matrix (Fin 2) (Fin 2) B) with hcdef
  have hcT : Matrix.vecMul c T = tangent m := by
    rw [hcdef, Matrix.vecMul_vecMul, ← hu, Units.inv_mul, Matrix.vecMul_one]
  have h0 : tangent (m - ∑ i, homothety (c i) (γ i)) = 0 := by
    rw [map_sub, tangent_sum_homothety, hcT, sub_self]
  obtain ⟨y, hy⟩ := (hker _).1 h0
  obtain ⟨ya, hya, yb, hyb, hyab⟩ : ∃ ya ∈ X.gradedPiece j (i₀ : ℕ),
      ∃ yb ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ), ya + yb = y := by
    have hy' : y ∈ X.gradedPiece j 0 ⊔ X.gradedPiece j 1 := by
      rw [hc.sup_eq_top]; exact AddSubgroup.mem_top y
    obtain ⟨y0, hy0, y1, hy1, rfl⟩ := AddSubgroup.mem_sup.1 hy'
    fin_cases i₀
    · exact ⟨y0, hy0, y1, hy1, rfl⟩
    · exact ⟨y1, hy1, y0, hy0, add_comm _ _⟩
  set r : CartierModule p X.F := homothety (c i₀) (γ i₀) + verschiebungInt yb with hr
  set q : CartierModule p X.F := homothety (c (i₀ + 1)) (γ (i₀ + 1)) + verschiebungInt ya with hq
  have hmrq : m = r + q := by
    have : m = (∑ i, homothety (c i) (γ i)) + verschiebungInt y := by
      rw [hy]; abel
    rw [this, hsum, ← hyab, map_add, hr, hq]
    abel
  have hr_mem : r ∈ X.gradedPiece j (i₀ : ℕ) := by
    refine (X.gradedPiece j (i₀ : ℕ)).add_mem (hhom _ _ _ (hγ.1 i₀)) ?_
    have := hV1 (i₀ + 1) yb hyb
    rwa [h10] at this
  have hq_mem : q ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ) :=
    (X.gradedPiece j _).add_mem (hhom _ _ _ (hγ.1 (i₀ + 1))) (hV1 i₀ ya hya)
  have hq0 : q = 0 := by
    refine hdisj q ?_ hq_mem
    have : q = m - r := by rw [hmrq]; abel
    rw [this]
    exact (X.gradedPiece j _).sub_mem hm hr_mem
  exact ⟨c i₀, yb, hyb, by rw [hmrq, hq0, add_zero]⟩

theorem exists_verschiebungInt_eq_varpi (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hker : ∀ f : CartierModule p X.F, tangent f = 0 ↔ ∃ g : CartierModule p X.F, verschiebungInt g = f)
    (i₀ : Fin 2) (h : CartierModule p X.F) (hPi : endAct X.varpiEnd (γ i₀) = verschiebungInt h)
    (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i₀ : ℕ)) :
    ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  obtain ⟨c, y, -, hmr⟩ := exists_eq_homothety_add_verschiebungInt j X hc γ hγ hker i₀ m hm
  refine ⟨homothety (c ^ p) h + endAct X.varpiEnd y, ?_⟩
  rw [hmr, map_add, map_add, endAct_homothety, hPi, homothety_verschiebungInt, endAct_verschiebungInt]

end K1LatticePlane

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (a ν : ℕ → Fin 2 → κ) (c : κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (hX4 : (X.map (TrivSqZeroExt.fstHom κ κ κ).toRingHom).HasHeight 4)
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    ∃ (z₁ z₂ : (X.toGradedCartierModuleData j hc).NMod)
      (hz₁ : z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀)
      (hz₂ : z₂ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀)
      (m₁ m₂ : CartierModule p X.F) (x₁ x₂ : DualNumber κ),
      (X.toGradedCartierModuleData j hc).vRange.mkQ m₁ =
        (X.toGradedCartierModuleData j hc).u L hL.isCartierLMap.map_verschiebung ⟨z₁, (AddSubgroup.mem_inf.mp hz₁).1⟩ ∧
      (X.toGradedCartierModuleData j hc).vRange.mkQ m₂ =
        (X.toGradedCartierModuleData j hc).u L hL.isCartierLMap.map_verschiebung ⟨z₂, (AddSubgroup.mem_inf.mp hz₂).1⟩ ∧
      tangent m₁ = x₁ • tangent (γ i₀) ∧ tangent m₂ = x₂ • tangent (γ i₀) ∧
      ∀ c₁ c₂ : ℤ, c₁ • TrivSqZeroExt.fst x₁ + c₂ • TrivSqZeroExt.fst x₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂ := by
  classical

  set φ : DualNumber κ →+* κ := (TrivSqZeroExt.fstHom κ κ κ).toRingHom with hφdef
  have hφ : ∀ r s : κ, φ (algebraMap κ (DualNumber κ) r + s • DualNumber.eps) = r := by
    intro r s
    simp [hφdef, TrivSqZeroExt.algebraMap_eq_inl]
  have hφsurj : Function.Surjective φ := fun r => ⟨algebraMap κ (DualNumber κ) r + (0 : κ) • DualNumber.eps, hφ r 0⟩
  have hφker : ∀ x y : DualNumber κ, φ x = 0 → φ y = 0 → x * y = 0 := by
    intro x y hx hy
    have hx' : x.fst = 0 := by simpa [hφdef] using hx
    have hy' : y.fst = 0 := by simpa [hφdef] using hy
    ext <;> simp [hx', hy']
  haveI : CharP (DualNumber κ) p := (Algebra.charP_iff κ (DualNumber κ) p).1 inferInstance
  have hpS : IsNilpotent ((p : ℕ) : DualNumber κ) := by
    rw [CharP.cast_eq_zero]; exact IsNilpotent.zero
  have hpκ : IsNilpotent ((p : ℕ) : κ) := by
    rw [CharP.cast_eq_zero]; exact IsNilpotent.zero
  have hom0 : ∀ f : CartierModule p X.F, homothety (0 : DualNumber κ) f = 0 := fun f => by
    rw [← teichmuller_smul, WittVector.teichmuller_zero]
    exact zero_smul (WittVector p (DualNumber κ)) f
  letI : Algebra ℤ_[p] (DualNumber κ) :=
    ((algebraMap κ (DualNumber κ)).comp ((ZMod.castHom (dvd_refl p) κ).comp (PadicInt.toZMod (p := p)))).toAlgebra
  obtain ⟨hV, -, hker, -⟩ :=
    MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
      p X.F

  obtain ⟨h, hh⟩ := hA i₀ 1
  have hPi : endAct X.varpiEnd (γ i₀) = verschiebungInt h := by
    rw [hh]
    simp [ha0, hν0, hom0]
  have hi : ∀ m' ∈ X.gradedPiece j (i₀ : ℕ), ∃ g : CartierModule p X.F,
      verschiebungInt g = endAct X.varpiEnd m' :=
    fun m' hm' => K1LatticePlane.exists_verschiebungInt_eq_varpi j X hc γ hγ hker i₀ h hPi m' hm'

  set Y : FormalODModule p κ := X.map φ with hY
  set j' : Zp2 p →+* κ := φ.comp j with hj'
  have hc' : IsCompl (Y.gradedPiece j' 0) (Y.gradedPiece j' 1) :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j' hpκ Y
  set γ' : Fin 2 → CartierModule p Y.F := fun i => baseChange φ (γ i) with hγ'
  have hγY : Y.IsHomogeneousVBasis j' γ' := hγ.map φ
  have hsep : IsHausdorff (Ideal.span {((p : ℕ) : κ)}) κ := by
    rw [Ideal.span_singleton_eq_bot.2 (CharP.cast_eq_zero κ p)]
    infer_instance
  obtain ⟨L', hL'⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData p j' hsep Y γ' hγY hc'
  have hA' : Y.HasStructureConstants γ'
      (fun m i => φ (algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps)) := hA.map φ

  obtain ⟨m₁, m₂, y₁, y₂, h1, h2, ht1, ht2, hind⟩ :=
    CerednikDrinfeld.FormalODModule.exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
      p κ j' Y hX4 γ' hγY hc' _ hA' i₀ (by show φ _ = 0; rw [hφ]; exact ha0)
      (by show φ _ ≠ 0; rw [hφ]; exact ha1) L' hL'

  have hF : X.F.map φ = Y.F := rfl
  obtain ⟨-, -, hbij⟩ :=
    CerednikDrinfeld.FormalODModule.nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
      p hpS φ hφsurj hφker j X γ hγ hc Y rfl j' rfl hc' hF (baseChangeEq φ hF) rfl
      (fun x => baseChangeEq_verschiebungInt φ hF x)
      (fun x => FormalODModule.baseChange_endAct_varpiEnd φ X x) L hL L' hL'

  have lift : ∀ (m₀ : CartierModule p Y.F) (y₀ : κ),
      (Y.toGradedCartierModuleData j' hc').nMk (m₀, 0) ∈
        (Y.toGradedCartierModuleData j' hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i₀ →
      tangent m₀ = y₀ • tangent (γ' i₀) →
      ∃ (z : (X.toGradedCartierModuleData j hc).NMod)
        (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀)
        (n : CartierModule p X.F) (x : DualNumber κ),
        (X.toGradedCartierModuleData j hc).vRange.mkQ n =
          (X.toGradedCartierModuleData j hc).u L hL.isCartierLMap.map_verschiebung
            ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩ ∧
        tangent n = x • tangent (γ i₀) ∧ TrivSqZeroExt.fst x = y₀ := by
    intro m₀ y₀ hm₀ htm₀
    obtain ⟨z, hz, hzimg⟩ := (hbij i₀).surjOn hm₀
    have hz' : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ := hz
    obtain ⟨n, hn, -, rfl⟩ :=
      (CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
        p j X hc hV L hL i₀ hi z).1 hz'
    obtain ⟨x, w, -, hnx⟩ :=
      K1LatticePlane.exists_eq_homothety_add_verschiebungInt j X hc γ hγ hker i₀ n hn
    have htn : tangent n = x • tangent (γ i₀) := by
      rw [hnx, map_add, tangent_homothety, tangent_verschiebungInt, add_zero]
    refine ⟨_, hz', n, x, rfl, htn, ?_⟩

    have himg : (Y.toGradedCartierModuleData j' hc').nMk (baseChangeEq φ hF n, 0) =
        (Y.toGradedCartierModuleData j' hc').nMk (m₀, 0) := by
      have e := hzimg
      rw [GradedCartierModuleData.nMap_nMk, map_zero] at e
      exact e
    have hdiff : (Y.toGradedCartierModuleData j' hc').nMk (baseChangeEq φ hF n - m₀, 0) = 0 := by
      have := congrArg (fun w => w - (Y.toGradedCartierModuleData j' hc').nMk (m₀, 0)) himg
      simp only [sub_self] at this
      rwa [← map_sub, Prod.mk_sub_mk, sub_zero] at this
    rw [GradedCartierModuleData.nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hdiff
    simp only [GradedCartierModuleData.nRel, LinearMap.mem_range] at hdiff
    obtain ⟨s, hs⟩ := hdiff
    rw [GradedCartierModuleData.nRelMap_apply] at hs
    have hs1 : verschiebungInt ((Y.toGradedCartierModuleData j' hc').ofSigma s) = baseChangeEq φ hF n - m₀ :=
      congrArg Prod.fst hs
    have htd : tangent (baseChangeEq φ hF n) = tangent m₀ := by
      have : tangent (baseChangeEq φ hF n - m₀) = 0 := by
        rw [← hs1]; exact tangent_verschiebungInt _
      rwa [map_sub, sub_eq_zero] at this
    have hγ'i : tangent (γ' i₀) = fun k => φ (tangent (γ i₀) k) := tangent_baseChangeEq φ rfl (γ i₀)
    have key : TrivSqZeroExt.fst x • tangent (γ' i₀) = y₀ • tangent (γ' i₀) := by
      rw [← htm₀, ← htd, tangent_baseChangeEq, htn, hγ'i]
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      rfl
    exact K1LatticePlane.smul_row_injective (Matrix.of fun i k => tangent (γ' i) k) hγY.2 i₀ _ _ key
  obtain ⟨z₁, hz₁, n₁, x₁, hq₁, htn₁, hx₁⟩ := lift m₁ y₁ h1 ht1
  obtain ⟨z₂, hz₂, n₂, x₂, hq₂, htn₂, hx₂⟩ := lift m₂ y₂ h2 ht2
  exact ⟨z₁, z₂, hz₁, hz₂, n₁, n₂, x₁, x₂, hq₁, hq₂, htn₁, htn₂, by rw [hx₁, hx₂]; exact hind⟩

end S_CerednikDrinfeld_FormalODModule_exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber (solution)
