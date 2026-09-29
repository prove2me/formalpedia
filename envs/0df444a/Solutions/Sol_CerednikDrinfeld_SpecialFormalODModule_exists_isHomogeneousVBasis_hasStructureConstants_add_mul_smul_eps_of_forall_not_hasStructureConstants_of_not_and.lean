-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a3bf4993-8c62-5f05-9cb6-a9a86b8210fb

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
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_hasStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace PenNF

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule
open scoped DualNumber

variable {k : Type u} [Field k]

noncomputable def rescale (c : k) : DualNumber k →ₐ[k] DualNumber k :=
  DualNumber.lift ⟨(Algebra.ofId k (DualNumber k), c • DualNumber.eps), by
    refine ⟨?_, fun a => ?_⟩
    · rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, smul_zero]
    · exact Commute.all _ _⟩

theorem rescale_apply (c : k) (t : DualNumber k) :
    rescale c t = algebraMap k (DualNumber k) t.fst + algebraMap k (DualNumber k) t.snd * (c • DualNumber.eps) :=
  DualNumber.lift_apply_apply _ t

theorem fst_rescale (c : k) (t : DualNumber k) : (rescale c t).fst = t.fst := by
  rw [rescale_apply]
  simp [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, Algebra.algebraMap_eq_smul_one]

theorem snd_rescale (c : k) (t : DualNumber k) : (rescale c t).snd = c * t.snd := by
  rw [rescale_apply]
  simp [DualNumber.snd_eps, Algebra.algebraMap_eq_smul_one, mul_comm]

theorem fstHom_comp_rescale (c : k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (rescale c).toRingHom = (TrivSqZeroExt.fstHom k k k).toRingHom :=
  RingHom.ext fun t => fst_rescale c t

theorem rescale_comp_algebraMap (c : k) :
    (rescale c).toRingHom.comp (algebraMap k (DualNumber k)) = algebraMap k (DualNumber k) :=
  (rescale c).comp_algebraMap

theorem rescale_const (c : k) (x y : k) :
    (rescale c).toRingHom (algebraMap k (DualNumber k) x + y • DualNumber.eps) =
      algebraMap k (DualNumber k) x + (c * y) • DualNumber.eps := by
  refine TrivSqZeroExt.ext ?_ ?_
  · show (rescale c _).fst = _
    rw [fst_rescale]; simp [DualNumber.fst_eps, Algebra.algebraMap_eq_smul_one]
  · show (rescale c _).snd = _
    rw [snd_rescale]; simp [DualNumber.snd_eps, Algebra.algebraMap_eq_smul_one]

theorem fstHom_comp_algebraMap :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k :=
  RingHom.ext fun x => by simp [Algebra.algebraMap_eq_smul_one]

theorem fst_const (x y : k) :
    (TrivSqZeroExt.fstHom k k k).toRingHom (algebraMap k (DualNumber k) x + y • DualNumber.eps) = x := by
  show TrivSqZeroExt.fst _ = x
  simp [DualNumber.fst_eps, Algebra.algebraMap_eq_smul_one]

theorem isHausdorff_span_charP (q : ℕ) [CharP k q] : IsHausdorff (Ideal.span {(q : k)}) k := by
  rw [show Ideal.span {(q : k)} = ⊥ from Ideal.span_singleton_eq_bot.mpr (CharP.cast_eq_zero k q)]
  infer_instance

end PenNF

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k))
    (ν : ℕ → Fin 2 → k) (hν0 : ∀ i, ν 0 i = 0)
    (hν : ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
        (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
            ((algebraMap k (DualNumber k)).comp j₀) γ' →
        ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
            (fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps))
    (N : FormalODModule q (DualNumber k))
    (w : (N.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    ∃ (c : k) (γN : Fin 2 → MvFormalGroup.CartierModule q N.F),
      N.IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γN ∧
      N.HasStructureConstants γN (fun m i => algebraMap k (DualNumber k) (a m i) + (c * ν m i) • DualNumber.eps) ∧
      ∀ i, MvFormalGroup.CartierModule.map w.toLawHom
          (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γN i)) = γ i := by

  classical

  have ha₁01 : (fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps) 0 0 *
      (fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps) 0 1 = (q : DualNumber k) := by
    simp only [hν0, zero_smul, add_zero, ← map_mul, h01, map_natCast]
  obtain ⟨X₁, γ₁, hγ₁, haγ₁⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
      q ((algebraMap k (DualNumber k)).comp j₀)
      (fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps) ha₁01

  have hγ₁r : (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom).IsHomogeneousVBasis j₀
      (fun i => MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)) := by
    have h := hγ₁.map (TrivSqZeroExt.fstHom k k k).toRingHom
    rwa [← RingHom.comp_assoc, PenNF.fstHom_comp_algebraMap, RingHom.id_comp] at h
  have haγ₁r : (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom).HasStructureConstants
      (fun i => MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)) a := by
    have h := haγ₁.map (TrivSqZeroExt.fstHom k k k).toRingHom
    have hfun : (fun m i => (TrivSqZeroExt.fstHom k k k).toRingHom
        ((fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps) m i)) = a := by
      funext m i; exact PenNF.fst_const (a m i) (ν m i)
    rwa [hfun] at h
  obtain ⟨w₁, hw₁, hw₁γ⟩ :=
    CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_hasStructureConstants q j₀
      (PenNF.isHausdorff_span_charP q) (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom) X₀.toFormalODModule
      (fun i => MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)) γ
      hγ₁r hγ a haγ₁r ha

  have h₁ : ∀ θ : X₁.Hom (X₀.toFormalODModule.map (algebraMap k (DualNumber k))), ¬ θ.IsIso := by
    intro θ hθ
    have h := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
      q ((algebraMap k (DualNumber k)).comp j₀) X₁ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))) θ hθ
      γ₁ hγ₁ (fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps) haγ₁
    exact hν _ h.1 h.2

  obtain ⟨c, hc⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
      X₀ hsmooth X₁ w₁ hw₁ h₁ N w hw
  obtain ⟨v, hv, hvw⟩ := hc (PenNF.rescale c).toRingHom (PenNF.fstHom_comp_rescale c) (PenNF.snd_rescale c)
  obtain ⟨vinv, hvinv₁, hvinv₂⟩ := hv
  have hvinv : vinv.IsIso := ⟨v, hvinv₂, hvinv₁⟩

  have hγ₁μ : (X₁.map (PenNF.rescale c).toRingHom).IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀)
      (fun i => MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)) := by
    have h := hγ₁.map (PenNF.rescale c).toRingHom
    rwa [← RingHom.comp_assoc, PenNF.rescale_comp_algebraMap] at h
  have haγ₁μ : (X₁.map (PenNF.rescale c).toRingHom).HasStructureConstants
      (fun i => MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i))
      (fun m i => algebraMap k (DualNumber k) (a m i) + (c * ν m i) • DualNumber.eps) := by
    have h := haγ₁.map (PenNF.rescale c).toRingHom
    have hfun : (fun m i => (PenNF.rescale c).toRingHom
        ((fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps) m i)) =
        (fun m i => algebraMap k (DualNumber k) (a m i) + (c * ν m i) • DualNumber.eps) := by
      funext m i; exact PenNF.rescale_const c (a m i) (ν m i)
    rwa [hfun] at h
  have hT := CerednikDrinfeld.FormalODModule.isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
      q ((algebraMap k (DualNumber k)).comp j₀) (X₁.map (PenNF.rescale c).toRingHom) N vinv hvinv
      (fun i => MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)) hγ₁μ
      (fun m i => algebraMap k (DualNumber k) (a m i) + (c * ν m i) • DualNumber.eps) haγ₁μ
  refine ⟨c, fun i => MvFormalGroup.CartierModule.map vinv.toLawHom
      (MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)), hT.1, hT.2, fun i => ?_⟩

  rw [← hw₁γ i]

  have hvS : MvPowerSeries.HasSubst (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (v.isODHom.map (TrivSqZeroExt.fstHom k k k).toRingHom).constantCoeff
  have hviS : MvPowerSeries.HasSubst (vinv.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (vinv.isODHom.map (TrivSqZeroExt.fstHom k k k).toRingHom).constantCoeff
  have hE : MvPowerSeries.HasSubst
      (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)).toPowerSeries :=
    (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)).hasSubst_toPowerSeries

  have hid : (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom).comp
      (vinv.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = Series.id k := by
    have h := congrArg (fun h => (FormalODModule.Hom.toSeries h).map (TrivSqZeroExt.fstHom k k k).toRingHom) hvinv₂
    beta_reduce at h
    rw [show (v.comp vinv).toSeries = v.toSeries.comp vinv.toSeries from rfl,
      show (FormalODModule.Hom.id _).toSeries = Series.id _ from rfl,
      Series.map_comp _ _ _ vinv.isODHom.constantCoeff, Series.map_id] at h
    exact h
  have hidfun : (fun s => MvPowerSeries.subst (vinv.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom)
      ((v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) s)) =
      (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k) := hid

  have hγμ : ∀ l, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom
      ((MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)).toPowerSeries l) =
      (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)).toPowerSeries l := by
    intro l
    show MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom
        (MvPowerSeries.map (PenNF.rescale c).toRingHom ((γ₁ i).toPowerSeries l)) =
      MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom ((γ₁ i).toPowerSeries l)
    rw [MvPowerSeries.map_map, PenNF.fstHom_comp_rescale]
  have hwj : ∀ j, w.toSeries j = MvPowerSeries.subst (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom)
      (w₁.toSeries j) := fun j => (congrFun hvw j).symm
  refine MvFormalGroup.CartierModule.ext (funext fun j => ?_)
  show MvPowerSeries.subst
      (fun l => MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom
        (MvPowerSeries.subst (MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)).toPowerSeries
          (vinv.toSeries l)))
      (w.toSeries j) =
    MvPowerSeries.subst (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)).toPowerSeries
      (w₁.toSeries j)
  have hinner : (fun l => MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom
        (MvPowerSeries.subst (MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)).toPowerSeries
          (vinv.toSeries l))) =
      fun l => MvPowerSeries.subst
        (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γ₁ i)).toPowerSeries
        ((vinv.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) l) := by
    funext l
    rw [MvPowerSeries.map_subst
      (MvFormalGroup.CartierModule.baseChange (PenNF.rescale c).toRingHom (γ₁ i)).hasSubst_toPowerSeries]
    congr 1
    · funext l'; exact hγμ l'
  rw [hinner, ← MvPowerSeries.subst_comp_subst_apply hviS hE, hwj j,
    MvPowerSeries.subst_comp_subst_apply hvS hviS, hidfun, MvPowerSeries.subst_self]
  rfl

end S_CerednikDrinfeld_SpecialFormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and (solution)
