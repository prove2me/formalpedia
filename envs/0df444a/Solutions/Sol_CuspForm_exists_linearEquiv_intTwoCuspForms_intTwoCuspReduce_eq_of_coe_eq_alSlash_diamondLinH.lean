-- Prove2me | solution 1 for CuspForm.exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/77a07624-f47c-5d1b-8884-be49d5d45260

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash
import Theorems.Thm_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
import Theorems.Thm_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct MatrixGroups ModularForm

set_option maxHeartbeats 3200000

open scoped TensorProduct MatrixGroups ModularForm

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul ext coe_smul coe_add intIdeal IntTwoCuspForms intTwoCuspReduce heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice twoCuspEnd coe_twoCuspEnd_apply gammaLift gamma0Units_gammaLift StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_alSlash_eq_pow_smul_diamondLinH"
namespace C2W
p2m_open "CuspForm"

open CongruenceSubgroup

section Diamond

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem diamondLinH_diamondLinH (k : ℤ) (a b : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.diamondLinH k a (CuspForm.diamondLinH k b f) = CuspForm.diamondLinH k (b * a) f := by
  have hD : CuspForm.StableD M H k := CuspForm.stableD M H k
  apply DFunLike.ext'
  rw [CuspForm.coe_diamondLinH_apply k hD a, CuspForm.coe_diamondLinH_apply k hD b,
    ← SlashAction.slash_mul, ← map_mul,
    CuspForm.coe_diamondLinH_eq_slash k hD (b * a) (CuspForm.gammaLift M b * CuspForm.gammaLift M a)
      (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift]) f]
  rfl

theorem diamondLinH_comm (k : ℤ) (a b : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.diamondLinH k a (CuspForm.diamondLinH k b f) = CuspForm.diamondLinH k b (CuspForm.diamondLinH k a f) := by
  rw [diamondLinH_diamondLinH, diamondLinH_diamondLinH, mul_comm]

theorem diamondLinH_one (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) : CuspForm.diamondLinH k 1 f = f := by
  have hD : CuspForm.StableD M H k := CuspForm.stableD M H k
  apply DFunLike.ext'
  rw [CuspForm.coe_diamondLinH_eq_slash k hD 1 1 (map_one _) f]
  show ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑f
  rw [map_one, SlashAction.slash_one]

theorem exists_alSlash_slash_eq_alSlash_diamondLinH {p : ℕ} (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ)
    (g : Gamma0 M) :
    ∃ δ : (ZMod M)ˣ, ∀ F : CuspForm (CohCarrier.GammaH M H) k,
      (ModularForm.alSlash W k ⇑F) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k δ F) := by
  have hD : CuspForm.StableD M H k := CuspForm.stableD M H k
  obtain ⟨δ, hδ, hW⟩ := W.exists_mem_Gamma0_alGL_mul_eq (g := (g : SL(2, ℤ))) g.2
  refine ⟨CohCarrier.gamma0Units M ⟨δ, hδ⟩, fun F => ?_⟩
  rw [ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, hW, SlashAction.slash_mul,
    CuspForm.coe_diamondLinH_eq_slash k hD _ ⟨δ, hδ⟩ rfl F]

end Diamond

section Square

variable (M : ℕ) [NeZero M] (p : ℕ) (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (W : ModularForm.AtkinLehnerDatum M p)

theorem exists_unitsMap_eq_natCast [Fact p.Prime] (hpM2 : ¬ p ^ 2 ∣ M) :
    ∃ d : (ZMod M)ˣ, (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : ZMod (M / p)) = (p : ZMod (M / p)) := by
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * c := by rw [hc]; ring
  obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) (ZMod.unitOfCoprime p hcop)
  exact ⟨d, by rw [hd, ZMod.coe_unitOfCoprime]⟩

include hHp in

theorem exists_forall_eq_diamondLinH_of_coe_eq_alSlash_of_coe_eq_alSlash
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : ZMod (M / p)) = (p : ZMod (M / p)))
    (e : (ZMod M)ˣ) :
    ∃ u : (ZMod M)ˣ, ∀ (f X₁ X₂ : CuspForm (CohCarrier.GammaH M H) 2),
      ⇑X₁ = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f) →
      ⇑X₂ = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e X₁) →
      X₂ = CuspForm.diamondLinH 2 u f := by
  have hD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2
  obtain ⟨δ, hδ⟩ := exists_alSlash_slash_eq_alSlash_diamondLinH (H := H) W 2 (CuspForm.gammaLift M e)
  refine ⟨e * δ * d, fun f X₁ X₂ h₁ h₂ => ?_⟩
  apply DFunLike.ext'

  have hX₁ : ⇑(CuspForm.diamondLinH 2 e X₁) =
      ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 δ (CuspForm.diamondLinH 2 e f)) := by
    rw [CuspForm.coe_diamondLinH_apply 2 hD e X₁, h₁, hδ]
  rw [h₂, hX₁, CuspForm.alSlash_alSlash_eq_pow_smul_diamondLinH M p hpM H hHp W 2 d hd, sub_self, zpow_zero, one_smul,
    diamondLinH_diamondLinH, diamondLinH_diamondLinH, mul_assoc]

end Square

section Integral

theorem diamondLinH_mem_twoCuspIntegralSet {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) {p : ℕ}
    {A : Subring ℂ} (u : (ZMod M)ˣ) {f : CuspForm (CohCarrier.GammaH M H) k}
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H k p A) :
    CuspForm.diamondLinH k u f ∈ CuspForm.twoCuspIntegralSet M H k p A :=
  CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet
    (by
      have := CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) k (.dia u)
      rwa [CuspForm.heckeGenH_dia] at this) hf

end Integral

end CuspForm.C2W

namespace GenT

theorem unitsMap_eq_one_iff_of_eq {M a b : ℕ} (hab : a = b) (h1 : a ∣ M) (h2 : b ∣ M) (u : (ZMod M)ˣ) :
    ZMod.unitsMap h1 u = 1 ↔ ZMod.unitsMap h2 u = 1 := by
  subst hab; rfl

theorem coe_diamondLinH_diamondLinH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) (d e : (ZMod M)ˣ)
    (X : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(CuspForm.diamondLinH k e (CuspForm.diamondLinH k d X)) = ⇑(CuspForm.diamondLinH k (d * e) X) := by
  have hD := CuspForm.stableD M H k
  rw [CuspForm.coe_diamondLinH_apply k hD e, CuspForm.coe_diamondLinH_apply k hD d, ← SlashAction.slash_mul,
    ← map_mul, CuspForm.coe_diamondLinH_eq_slash k hD (d * e) (CuspForm.gammaLift M d * CuspForm.gammaLift M e)
      (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift]) X]
  rfl

theorem exists_unit_crt (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (c : (ZMod p)ˣ) (e : (ZMod (M / p))ˣ) :
    ∃ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = e ∧ ZMod.castHom hpM (ZMod p) (u : ZMod M) = c := by
  have hp : p.Prime := Fact.out
  have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hpM2
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by rw [pow_two, mul_assoc, ← ht]; exact hM⟩
  let E : ZMod M ≃+* ZMod p × ZMod (M / p) := (ZMod.ringEquivCongr hM).trans (ZMod.chineseRemainder hcop)
  have hE1 : (RingHom.fst _ _).comp E.toRingHom = ZMod.castHom hpM (ZMod p) := Subsingleton.elim _ _
  have hE2 : (RingHom.snd _ _).comp E.toRingHom = ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) :=
    Subsingleton.elim _ _
  refine ⟨Units.map E.symm.toRingHom.toMonoidHom (MulEquiv.prodUnits.symm (c, e)), ?_, ?_⟩
  · apply Units.ext
    show ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) (E.symm ((MulEquiv.prodUnits.symm (c, e) : (ZMod p × ZMod (M / p))ˣ) : ZMod p × ZMod (M / p))) = (e : ZMod (M / p))
    rw [← hE2, RingHom.comp_apply]
    show (E (E.symm _)).2 = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  · show ZMod.castHom hpM (ZMod p) (E.symm ((MulEquiv.prodUnits.symm (c, e) : (ZMod p × ZMod (M / p))ˣ) : ZMod p × ZMod (M / p))) = (c : ZMod p)
    rw [← hE1, RingHom.comp_apply]
    show (E (E.symm _)).1 = _
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem units_eq_of_unitsMap_eq (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (u w : (ZMod M)ˣ) (hR : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) w)
    (hp' : ZMod.unitsMap hpM u = ZMod.unitsMap hpM w) : u = w := by
  have hp : p.Prime := Fact.out
  have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hpM2
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by rw [pow_two, mul_assoc, ← ht]; exact hM⟩
  let E : ZMod M ≃+* ZMod p × ZMod (M / p) := (ZMod.ringEquivCongr hM).trans (ZMod.chineseRemainder hcop)
  have hE1 : (RingHom.fst _ _).comp E.toRingHom = ZMod.castHom hpM (ZMod p) := Subsingleton.elim _ _
  have hE2 : (RingHom.snd _ _).comp E.toRingHom = ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) :=
    Subsingleton.elim _ _
  apply Units.ext
  apply E.injective
  refine Prod.ext ?_ ?_
  · have h := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) hp'
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe] at h
    rw [← hE1] at h
    exact h
  · have h := congrArg (fun x : (ZMod (M / p))ˣ => (x : ZMod (M / p))) hR
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe] at h
    rw [← hE2] at h
    exact h

end GenT

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul ext coe_smul coe_add intIdeal IntTwoCuspForms intTwoCuspReduce heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice twoCuspEnd coe_twoCuspEnd_apply gammaLift gamma0Units_gammaLift StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_alSlash_eq_pow_smul_diamondLinH"
namespace WTransportCL
p2m_open "CuspForm"
theorem diamondLinH_mem_heckeRingH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (d : (ZMod M)ˣ) :
    (CuspForm.diamondLinH (H := H) k d) ∈ CuspForm.heckeRingH M H k := by
  have := CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) k (.dia d)
  rwa [CuspForm.heckeGenH_dia] at this
end CuspForm.WTransportCL

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul ext coe_smul coe_add intIdeal IntTwoCuspForms intTwoCuspReduce heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice twoCuspEnd coe_twoCuspEnd_apply gammaLift gamma0Units_gammaLift StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_alSlash_eq_pow_smul_diamondLinH"
namespace HeckeStabS
p2m_open "CuspForm"

open GenT

def NaiveD (p : ℕ) {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (h : CuspForm (CohCarrier.GammaH M H) 2) : Prop :=
  ∀ (d : (ZMod M)ˣ) (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
    ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d h)) n ∈ (⊥ : Subring ℂ) ∧
      ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 d h)) n ∈ (⊥ : Subring ℂ)

theorem naiveD_diamondLinH (p : ℕ) {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (d₀ : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hS : NaiveD p f) : NaiveD p (CuspForm.diamondLinH 2 d₀ f) := by
  intro d W n
  rw [coe_diamondLinH_diamondLinH 2 d₀ d f]
  exact hS (d₀ * d) W n

end CuspForm.HeckeStabS

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul ext coe_smul coe_add intIdeal IntTwoCuspForms intTwoCuspReduce heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice twoCuspEnd coe_twoCuspEnd_apply gammaLift gamma0Units_gammaLift StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_alSlash_eq_pow_smul_diamondLinH"
namespace HeckeStabS
p2m_open "CuspForm"

open GenT

theorem naiveD_of_coe_eq_alSlash_diamondLinH_of_mem_twoCuspIntegralSet
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : ⇑g = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) :
    NaiveD p g := by
  classical
  intro d W' n

  obtain ⟨ds, hdsR, hdsp⟩ := exists_unit_crt M p hpM hpM2 (ZMod.unitsMap hpM d)⁻¹ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)
  obtain ⟨d', hd'R, hd'p, hW⟩ := CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash M p hpM H hHp W 2 ds
    (CuspForm.diamondLinH 2 e f) g hg
  have hdsp' : ZMod.unitsMap hpM ds = (ZMod.unitsMap hpM d)⁻¹ := by
    apply Units.ext
    simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe]
    exact hdsp
  have hd' : d' = d := by
    apply units_eq_of_unitsMap_eq M p hpM hpM2
    · rw [hd'R, hdsR]
    · rw [map_mul, hdsp'] at hd'p
      exact (mul_inv_eq_one.mp hd'p)
  rw [← hd', ← hW, coe_diamondLinH_diamondLinH 2 e ds f]
  have hmem : (CuspForm.diamondLinH (H := H) 2 (e * ds)) ∈ CuspForm.heckeRingH M H 2 :=
    CuspForm.WTransportCL.diamondLinH_mem_heckeRingH M H 2 (e * ds)
  refine ⟨(hf _ hmem W n).2, ?_⟩
  obtain ⟨δ, hδ⟩ := CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH M p hpM H hHp W' W 2
    (CuspForm.diamondLinH 2 (e * ds) f)
  rw [hδ, show ((2 : ℤ) - 2) = 0 by norm_num, zpow_zero, one_smul]
  have hmul : (CuspForm.diamondLinH (H := H) 2 δ * CuspForm.diamondLinH 2 (e * ds)) ∈ CuspForm.heckeRingH M H 2 :=
    (CuspForm.heckeRingH M H 2).mul_mem (CuspForm.WTransportCL.diamondLinH_mem_heckeRingH M H 2 δ) hmem
  have := (hf _ hmul W n).1
  rwa [Module.End.mul_apply] at this

end CuspForm.HeckeStabS

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul ext coe_smul coe_add intIdeal IntTwoCuspForms intTwoCuspReduce heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice twoCuspEnd coe_twoCuspEnd_apply gammaLift gamma0Units_gammaLift StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_alSlash_eq_pow_smul_diamondLinH"
namespace WTransportCL
p2m_open "CuspForm"

open ModularForm

theorem R_eq_div {M p : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p) : W.R = M / p :=
  (Nat.div_eq_of_eq_mul_left W.q_pos (W.hM.trans (mul_comm _ _))).symm

theorem hHp_of_hHp {M p : ℕ} [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
  intro u hu
  refine hHp u ?_
  have key : ∀ (n : ℕ) (h : n ∣ M), n = M / p → ZMod.unitsMap h u = 1 →
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 := by
    rintro n h rfl h1; exact h1
  exact key W.R (Dvd.intro_left p W.hM.symm) (R_eq_div W) hu

section Omega

theorem exists_coe_eq {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    ∃ X : CuspForm (CohCarrier.GammaH M H) 2, ⇑X = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f) :=
  CuspForm.exists_GammaH_coe_eq_alSlash (Fact.out : p.Prime) W H (hHp_of_hHp hpM H hHp W) 2 _

noncomputable def omegaLin {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ) : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2 where
  toFun f := Classical.choose (exists_coe_eq hpM H hHp W e f)
  map_add' f f' := by
    apply DFunLike.coe_injective
    show ⇑(Classical.choose (exists_coe_eq hpM H hHp W e (f + f'))) =
      ⇑(Classical.choose (exists_coe_eq hpM H hHp W e f) + Classical.choose (exists_coe_eq hpM H hHp W e f'))
    rw [CuspForm.coe_add, Classical.choose_spec (exists_coe_eq hpM H hHp W e (f + f')),
      Classical.choose_spec (exists_coe_eq hpM H hHp W e f), Classical.choose_spec (exists_coe_eq hpM H hHp W e f'),
      map_add, CuspForm.coe_add, ModularForm.alSlash_add]
  map_smul' c f := by
    apply DFunLike.coe_injective
    show ⇑(Classical.choose (exists_coe_eq hpM H hHp W e (c • f))) =
      ⇑((RingHom.id ℂ c) • Classical.choose (exists_coe_eq hpM H hHp W e f))
    rw [RingHom.id_apply, CuspForm.IsGLPos.coe_smul, Classical.choose_spec (exists_coe_eq hpM H hHp W e (c • f)),
      Classical.choose_spec (exists_coe_eq hpM H hHp W e f), map_smul, CuspForm.IsGLPos.coe_smul,
      ModularForm.alSlash_smul]

theorem coe_omegaLin {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    ⇑(omegaLin hpM H hHp W e f) = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f) :=
  Classical.choose_spec (exists_coe_eq hpM H hHp W e f)

theorem eq_omegaLin_of_coe_eq {p : ℕ} [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) : g = omegaLin hpM H hHp W e f :=
  DFunLike.coe_injective (hg.trans (coe_omegaLin hpM H hHp W e f).symm)

end Omega

end CuspForm.WTransportCL

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul ext coe_smul coe_add intIdeal IntTwoCuspForms intTwoCuspReduce heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet twoCuspLattice twoCuspIntegralSet_subset_twoCuspLattice twoCuspEnd coe_twoCuspEnd_apply gammaLift gamma0Units_gammaLift StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_alSlash_eq_pow_smul_diamondLinH"
namespace WTransport
p2m_open "CuspForm"

open ModularForm CuspForm.WTransportCL CuspForm.C2W
open scoped MatrixGroups

section Generic

variable {A : Type*} [CommRing A] {L : Type*} [AddCommGroup L] [Module A L] (I : Ideal A)

theorem smul_top_le_comap (φ : L →ₗ[A] L) :
    (I • ⊤ : Submodule A L) ≤ (I • ⊤ : Submodule A L).comap φ := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

def descend (φ : L →ₗ[A] L) : (L ⧸ (I • ⊤ : Submodule A L)) →ₗ[A] (L ⧸ (I • ⊤ : Submodule A L)) :=
  Submodule.mapQ _ _ φ (smul_top_le_comap I φ)

@[scoped simp] theorem descend_mkQ (φ : L →ₗ[A] L) (x : L) :
    descend I φ ((I • ⊤ : Submodule A L).mkQ x) = (I • ⊤ : Submodule A L).mkQ (φ x) := rfl

theorem descend_id : descend I (LinearMap.id : L →ₗ[A] L) = LinearMap.id := by
  ext x; rfl

theorem descend_comp (φ ψ : L →ₗ[A] L) : descend I (φ ∘ₗ ψ) = descend I φ ∘ₗ descend I ψ := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (I • ⊤ : Submodule A L) x
  rfl

def descendEquiv (e : L ≃ₗ[A] L) : (L ⧸ (I • ⊤ : Submodule A L)) ≃ₗ[A] (L ⧸ (I • ⊤ : Submodule A L)) :=
  LinearEquiv.ofLinear (descend I e.toLinearMap) (descend I e.symm.toLinearMap)
    (by rw [← descend_comp, show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from
          LinearMap.ext fun x => e.apply_symm_apply x, descend_id])
    (by rw [← descend_comp, show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from
          LinearMap.ext fun x => e.symm_apply_apply x, descend_id])

theorem bijective_descend_of_comp_self (φ : L →ₗ[A] L) (e : L ≃ₗ[A] L) (h : φ ∘ₗ φ = e.toLinearMap) :
    Function.Bijective (descend I φ) := by
  have hc : descend I φ ∘ₗ descend I φ = (descendEquiv I e).toLinearMap := by
    rw [← descend_comp, h]; rfl
  constructor
  · intro x y hxy
    have := congrArg (descend I φ) hxy
    rw [← LinearMap.comp_apply (f := descend I φ), ← LinearMap.comp_apply (f := descend I φ), hc] at this
    exact (descendEquiv I e).injective this
  · intro z
    refine ⟨descend I φ ((descendEquiv I e).symm z), ?_⟩
    rw [← LinearMap.comp_apply (f := descend I φ), hc]
    exact (descendEquiv I e).apply_symm_apply z

end Generic

section Assembly

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)

local notation "Lz" => CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)

noncomputable def restrictLattice (ω : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hω : ∀ f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ), ω f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    Lz →ₗ[(⊥ : Subring ℂ)] Lz where
  toFun x := ⟨ω x, by
    obtain ⟨x, hx⟩ := x
    show ω x ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)
    unfold CuspForm.twoCuspLattice at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hω y hy)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
        rw [show ω (a • y) = a • ω y from by rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smul]]
        exact Submodule.smul_mem _ a hy⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' a x := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply, Subring.smul_def, LinearMap.map_smul])

@[scoped simp] theorem coe_restrictLattice_apply (ω : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hω : ∀ f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ), ω f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (x : Lz) : ((restrictLattice p M H ω hω x : Lz) : CuspForm (CohCarrier.GammaH M H) 2) = ω x := rfl

noncomputable def diamondLatticeEquiv (u : (ZMod M)ˣ) : Lz ≃ₗ[(⊥ : Subring ℂ)] Lz :=
  LinearEquiv.ofLinear
    (CuspForm.twoCuspEnd ⟨CuspForm.diamondLinH 2 u, diamondLinH_mem_heckeRingH M H 2 u⟩)
    (CuspForm.twoCuspEnd ⟨CuspForm.diamondLinH 2 u⁻¹, diamondLinH_mem_heckeRingH M H 2 u⁻¹⟩)
    (LinearMap.ext fun x => Subtype.ext (by
      simp only [LinearMap.comp_apply, CuspForm.coe_twoCuspEnd_apply, LinearMap.id_apply]
      rw [diamondLinH_diamondLinH, inv_mul_cancel, diamondLinH_one]))
    (LinearMap.ext fun x => Subtype.ext (by
      simp only [LinearMap.comp_apply, CuspForm.coe_twoCuspEnd_apply, LinearMap.id_apply]
      rw [diamondLinH_diamondLinH, mul_inv_cancel, diamondLinH_one]))

include hpM hpM2 hHp in

theorem exists_linearEquiv :
    ∃ ωW : CuspForm.IntTwoCuspForms M H p ≃ₗ[ZMod p] CuspForm.IntTwoCuspForms M H p,
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
        (g : CuspForm (CohCarrier.GammaH M H) 2), ⇑g = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f) →
        ∃ hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ),
          ωW (CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) =
            CuspForm.intTwoCuspReduce M H p ⟨g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hg⟩ := by
  classical

  let ω := omegaLin hpM H hHp W e
  have hω : ∀ f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ), ω f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    fun f hf => CuspForm.mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem p M hpM hpM2 H hHp (ω f)
      (CuspForm.HeckeStabS.naiveD_of_coe_eq_alSlash_diamondLinH_of_mem_twoCuspIntegralSet p M hpM hpM2 H hHp W e f hf
        (ω f) (coe_omegaLin hpM H hHp W e f))
  let φ : Lz →ₗ[(⊥ : Subring ℂ)] Lz := restrictLattice p M H ω hω

  obtain ⟨d, hd⟩ := exists_unitsMap_eq_natCast M p hpM hpM2
  obtain ⟨u, hu⟩ := exists_forall_eq_diamondLinH_of_coe_eq_alSlash_of_coe_eq_alSlash M p hpM H hHp W d hd e
  have hsq : φ ∘ₗ φ = (diamondLatticeEquiv p M H u).toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show ω (ω x) = CuspForm.diamondLinH 2 u x
    exact hu x (ω x) (ω (ω x)) (coe_omegaLin hpM H hHp W e x) (coe_omegaLin hpM H hHp W e (ω x))

  have hbij := bijective_descend_of_comp_self (CuspForm.intIdeal p) φ (diamondLatticeEquiv p M H u) hsq
  let ψ : CuspForm.IntTwoCuspForms M H p →+ CuspForm.IntTwoCuspForms M H p :=
    (descend (CuspForm.intIdeal p) φ).toAddMonoidHom
  have hψbij : Function.Bijective ψ := hbij
  let ωW : CuspForm.IntTwoCuspForms M H p ≃ₗ[ZMod p] CuspForm.IntTwoCuspForms M H p :=
    LinearEquiv.ofBijective (ψ.toZModLinearMap p) hψbij
  refine ⟨ωW, fun f hf g hg => ?_⟩
  have hgI : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem p M hpM hpM2 H hHp g
      (CuspForm.HeckeStabS.naiveD_of_coe_eq_alSlash_diamondLinH_of_mem_twoCuspIntegralSet p M hpM hpM2 H hHp W e f hf g hg)
  refine ⟨hgI, ?_⟩
  have hgω : g = ω f := eq_omegaLin_of_coe_eq hpM H hHp W e f g hg

  show descend (CuspForm.intIdeal p) φ ((CuspForm.intIdeal p • ⊤ : Submodule (⊥ : Subring ℂ) Lz).mkQ _) =
    (CuspForm.intIdeal p • ⊤ : Submodule (⊥ : Subring ℂ) Lz).mkQ _
  rw [descend_mkQ]
  congr 1
  exact Subtype.ext hgω.symm

end Assembly

end CuspForm.WTransport
p2m_reactivate "P2MW.S_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH.CuspForm P2MW.S_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH.CuspForm.WTransport"
p2m_reactivate "P2MW.S_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH.CuspForm"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ) :
    ∃ ωW : CuspForm.IntTwoCuspForms M H p ≃ₗ[ZMod p] CuspForm.IntTwoCuspForms M H p,
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
        (g : CuspForm (CohCarrier.GammaH M H) 2), ⇑g = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f) →
        ∃ hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ),
          ωW (CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) = CuspForm.intTwoCuspReduce M H p ⟨g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hg⟩ :=
  CuspForm.WTransport.exists_linearEquiv p M hpM hpM2 H hHp W e

end S_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
end P2MW
export P2MW.S_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH (solution)
