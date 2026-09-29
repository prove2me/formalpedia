-- Prove2me | solution 1 for CuspForm.forall_qCoeff_diamondLinH_heckeGenH_mem_of_forall_qCoeff_diamondLinH_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b5a18fbf-09dd-5c41-b559-f1495b0d18ab

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash
import Theorems.Thm_CuspForm_alSlash_coe_heckeTLinH_eq_coe_heckeTLinH
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
import Theorems.Thm_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH
import Theorems.Thm_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
import Theorems.Thm_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash
import Theorems.Thm_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_forall_qCoeff_diamondLinH_heckeGenH_mem_of_forall_qCoeff_diamondLinH_mem
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct MatrixGroups ModularForm

namespace CuspForm
p2m_export "CuspForm" "smul_apply coe_sub ext coe_add heckeGenH heckeGenH_T heckeGenH_U heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet gammaLift gamma0Units_gammaLift unitOfPrimeNotDvd StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash heckeULinH coe_heckeULinH_apply heckeTLinH qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash alSlash_coe_heckeTLinH_eq_coe_heckeTLinH heckeTLinH_heckeULinH_diamondLinH_comm exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_coe_heckeULinH_eq_coe_heckeULinH qCoeff_heckeULinH_eq_qCoeff_mul exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash alSlash_alSlash_eq_pow_smul_diamondLinH stableU"
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

namespace GenUS

open ModularFormClass CohCarrier CongruenceSubgroup

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem gammaLift_mem_GammaH_of_mem {u : (ZMod M)ˣ} (hu : u ∈ H) :
    ((CuspForm.gammaLift M u : Gamma0 M) : SL(2, ℤ)) ∈ GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  exact ⟨(CuspForm.gammaLift M u).2, by
    rw [show (⟨((CuspForm.gammaLift M u : Gamma0 M) : SL(2, ℤ)), (CuspForm.gammaLift M u).2⟩ : Gamma0 M) =
      CuspForm.gammaLift M u from rfl, CuspForm.gamma0Units_gammaLift]; exact hu⟩

theorem diamondLinH_of_mem (k : ℤ) {u : (ZMod M)ˣ} (hu : u ∈ H) (g : CuspForm (GammaH M H) k) :
    CuspForm.diamondLinH k u g = g := by
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k)]
  exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ (gammaLift_mem_GammaH_of_mem hu))

theorem diamondLinH_diamondLinH (k : ℤ) (d e : (ZMod M)ˣ) (g : CuspForm (GammaH M H) k) :
    CuspForm.diamondLinH k d (CuspForm.diamondLinH k e g) = CuspForm.diamondLinH k (e * d) g := by
  have hD := CuspForm.stableD M H k
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_diamondLinH_apply k hD d, CuspForm.coe_diamondLinH_apply k hD e, ← SlashAction.slash_mul,
    ← map_mul]
  have : ((CuspForm.gammaLift M e : Gamma0 M) : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) =
      ((CuspForm.gammaLift M e * CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) := rfl
  rw [this, CuspForm.coe_diamondLinH_eq_slash k hD (e * d) (CuspForm.gammaLift M e * CuspForm.gammaLift M d)
    (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift])]

theorem diamondLinH_inv_diamondLinH (k : ℤ) (d : (ZMod M)ˣ) (g : CuspForm (GammaH M H) k) :
    CuspForm.diamondLinH k d⁻¹ (CuspForm.diamondLinH k d g) = g := by
  rw [diamondLinH_diamondLinH, mul_inv_cancel]
  exact diamondLinH_of_mem k (one_mem H) g

variable {p : ℕ} [Fact p.Prime]

theorem coprime_p_div (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : Nat.Coprime p (M / p) := by
  have hp : p.Prime := Fact.out
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpM2 ?_
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    _ = p ^ 2 * c := by rw [hc]; ring

theorem exists_unit_eq_p (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ∃ d₁ : (ZMod M)ˣ, (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d₁ : ZMod (M / p)) = (p : ZMod (M / p)) := by
  obtain ⟨d₁, hd₁⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM)
    (ZMod.unitOfCoprime p (coprime_p_div hpM hpM2))
  exact ⟨d₁, by rw [hd₁, ZMod.coe_unitOfCoprime]⟩

theorem R_eq (W : ModularForm.AtkinLehnerDatum M p) : W.R = M / p := by
  have hp : p.Prime := Fact.out
  calc W.R = p * W.R / p := (Nat.mul_div_cancel_left _ hp.pos).symm
    _ = M / p := by rw [← W.hM]

theorem unitsMap_R_eq_one_iff (hpM : p ∣ M) (W : ModularForm.AtkinLehnerDatum M p) (u : (ZMod M)ˣ) :
    ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 ↔ ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 := by
  have key : ∀ (R : ℕ) (hR : R ∣ M), R = M / p →
      (ZMod.unitsMap hR u = 1 ↔ ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1) := by
    intro R hR h; subst h; exact Iff.rfl
  exact key W.R _ (R_eq W)

theorem hHp_R (hpM : p ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H :=
  fun u hu => hHp u ((unitsMap_R_eq_one_iff hpM W u).mp hu)

theorem unitsMap_R_coe_eq_p (hpM : p ∣ M) (W : ModularForm.AtkinLehnerDatum M p) (d₁ : (ZMod M)ˣ)
    (hd₁ : (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d₁ : ZMod (M / p)) = (p : ZMod (M / p))) :
    (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d₁ : ZMod W.R) = (p : ZMod W.R) := by
  have key : ∀ (R : ℕ) (hR : R ∣ M), R = M / p → ((ZMod.unitsMap hR d₁ : ZMod R) = (p : ZMod R)) := by
    intro R hR h; subst h; exact hd₁
  exact key W.R _ (R_eq W)

end GenUS

namespace GenUS

open ModularFormClass CohCarrier CongruenceSubgroup

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime]

theorem one_mem_strictPeriods (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    (1 : ℝ) ∈ ((GammaH N H' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH N H')]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_coe_add (f g : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  unfold qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M H) f g, map_add]

theorem qCoeff_coe_sub (f g : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  unfold qCoeff
  rw [CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M H) f g, map_sub]

theorem qCoeff_smul_coe (c : ℂ) (f : CuspForm (GammaH M H) 2) (n : ℕ) :
    qCoeff (c • ⇑f) n = c * qCoeff (⇑f) n := by
  unfold qCoeff
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M H) c f]
  simp

def Naive (p : ℕ) (A : Subring ℂ) (g : CuspForm (GammaH M H) 2) : Prop :=
  ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
    qCoeff (⇑g) n ∈ A ∧ qCoeff (ModularForm.alSlash W 2 ⇑g) n ∈ A

theorem alSlash_sub (W : ModularForm.AtkinLehnerDatum M p) (k : ℤ) (a b : UpperHalfPlane → ℂ) :
    ModularForm.alSlash W k (a - b) = ModularForm.alSlash W k a - ModularForm.alSlash W k b := by
  simp only [ModularForm.alSlash_def, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash]

section Main

variable (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  {A : Subring ℂ}
include hpM hHp

def NaiveS (p : ℕ) (A : Subring ℂ) (g : CuspForm (GammaH M H) 2) : Prop :=
  ∀ d : (ZMod M)ˣ, Naive p A (CuspForm.diamondLinH 2 d g)

omit hpM hHp in
theorem NaiveS.naive {g : CuspForm (GammaH M H) 2} (hg : NaiveS p A g) : Naive p A g := by
  have := hg 1
  rwa [diamondLinH_of_mem 2 (one_mem H)] at this

omit hpM hHp in

theorem NaiveS.diamondLinH {g : CuspForm (GammaH M H) 2} (hg : NaiveS p A g) (e : (ZMod M)ˣ) :
    NaiveS p A (CuspForm.diamondLinH 2 e g) := fun d => by
  rw [diamondLinH_diamondLinH]; exact hg (e * d)

omit hpM hHp in

theorem exists_coe_diamondLinH_eq_alSlash_diamondLinH (W : ModularForm.AtkinLehnerDatum M p) (d : (ZMod M)ˣ)
    (g X : CuspForm (GammaH M H) 2) (hX : ⇑X = ModularForm.alSlash W 2 ⇑g) :
    ∃ δ : (ZMod M)ˣ, ⇑(CuspForm.diamondLinH 2 d X) = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 δ g) := by
  have hD := CuspForm.stableD M H 2
  obtain ⟨δ, hδ, hW⟩ := W.exists_mem_Gamma0_alGL_mul_eq (g := ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)))
    (CuspForm.gammaLift M d).2
  refine ⟨CohCarrier.gamma0Units M ⟨δ, hδ⟩, ?_⟩
  rw [CuspForm.coe_diamondLinH_apply 2 hD d X, hX, ModularForm.alSlash_def, ModularForm.alSlash_def,
    ← SlashAction.slash_mul, hW, SlashAction.slash_mul, CuspForm.coe_diamondLinH_eq_slash 2 hD _ ⟨δ, hδ⟩ rfl g]

theorem exists_X (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (GammaH M H) 2) (hf : NaiveS p A f) :
    ∃ X : CuspForm (GammaH M H) 2, ⇑X = ModularForm.alSlash W 2 ⇑f ∧ NaiveS p A X := by
  have hp : p.Prime := Fact.out
  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H (hHp_R hpM hHp W) 2 f
  refine ⟨X, hX, fun d W' n => ?_⟩
  obtain ⟨δ, hδ⟩ := exists_coe_diamondLinH_eq_alSlash_diamondLinH W d f X hX
  refine ⟨?_, ?_⟩
  · rw [hδ]; exact ((hf δ) W n).2
  · obtain ⟨δ', hδ'⟩ := CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH M p hpM H hHp W' W 2
      (CuspForm.diamondLinH 2 δ f)
    have h1 : ((p : ℂ) ^ ((2 : ℤ) - 2)) = 1 := by norm_num
    rw [hδ, hδ', h1, one_smul, diamondLinH_diamondLinH]
    exact ((hf (δ * δ')) W' n).1

omit hpM hHp in

theorem naive_heckeULinH_of_ne' (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (GammaH M H) 2) (hf : Naive p A f) : Naive p A (CuspForm.heckeULinH 2 q f) := by
  have hp : p.Prime := Fact.out
  intro W n
  refine ⟨?_, ?_⟩
  · rw [CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hq hqM]; exact (hf W (n * q)).1
  · obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H (hHp_R hpM hHp W) 2 f
    rw [CuspForm.alSlash_coe_heckeULinH_eq_coe_heckeULinH M p hpM H hHp W 2 hq hqM hqp f X hX,
      CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hq hqM, hX]
    exact (hf W (n * q)).2

theorem naive_diamondLinH_heckeULinH_self (d₁ : (ZMod M)ˣ)
    (hd₁ : (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d₁ : ZMod (M / p)) = (p : ZMod (M / p)))
    (f : CuspForm (GammaH M H) 2) (hf : NaiveS p A f) :
    Naive p A (CuspForm.diamondLinH 2 d₁ (CuspForm.heckeULinH 2 p f)) := by
  have hp : p.Prime := Fact.out
  have hcomm := (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H 2).2.2.2.1 p hp hpM
  set Y : CuspForm (GammaH M H) 2 := CuspForm.diamondLinH 2 d₁ (CuspForm.heckeULinH 2 p f) with hYdef
  show Naive p A Y
  have hYcomm : Y = CuspForm.heckeULinH 2 p (CuspForm.diamondLinH 2 d₁ f) := by rw [hYdef, hcomm]
  intro W n
  refine ⟨?_, ?_⟩
  ·
    rw [hYcomm, CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hp hpM]
    exact ((hf d₁) W (n * p)).1
  ·
    haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
    obtain ⟨X, hX, hXN⟩ := exists_X hpM hHp W f hf
    obtain ⟨G, hG⟩ := CuspForm.exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash hp W H
      (hHp_R hpM hHp W) 2 X d₁ (unitsMap_R_coe_eq_p hpM W d₁ hd₁)
    have h0 : ((p : ℂ) ^ ((2 : ℤ) - 2)) = 1 := by norm_num
    have hXX : ModularForm.alSlash W 2 ⇑X = ⇑(CuspForm.diamondLinH 2 d₁ f) := by
      rw [hX, CuspForm.alSlash_alSlash_eq_pow_smul_diamondLinH M p hpM H hHp W 2 d₁ hd₁ f, h0, one_smul]
    have hU : ModularForm.heckeU 2 p ⇑(CuspForm.diamondLinH 2 d₁ f) = ⇑Y := by
      rw [hYcomm, CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hp hpM)]

    set Gt : CuspForm (GammaH M H) 2 := CuspForm.diamondLinH 2 d₁ X + Y with hGt
    have hGGt : ⇑G = ⇑Gt := by
      rw [hG, hXX, hU, h0, one_smul, hGt, CuspForm.coe_add]
    have hYeq : (⇑Y : UpperHalfPlane → ℂ) = ⇑Gt - ⇑(CuspForm.diamondLinH 2 d₁ X) := by
      rw [hGt, CuspForm.coe_add]; abel

    obtain ⟨Z₁, hZ₁⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H (hHp_R hpM hHp W) 2 Gt
    obtain ⟨Z₂, hZ₂⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H (hHp_R hpM hHp W) 2 (CuspForm.diamondLinH 2 d₁ X)
    have hslash : ModularForm.alSlash W 2 ⇑Y = ⇑(Z₁ - Z₂) := by
      rw [hYeq, alSlash_sub, ← hZ₁, ← hZ₂, CuspForm.coe_sub]
    rw [hslash, qCoeff_coe_sub]
    refine A.sub_mem ?_ ?_
    swap
    · rw [hZ₂]; exact ((hXN d₁) W n).2

    set d₀ : (ZMod W.R)ˣ := ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d₁ with hd₀def
    have hd₀ : (d₀ : ZMod W.R) = (p : ZMod W.R) := unitsMap_R_coe_eq_p hpM W d₁ hd₁
    have hLS := ModularForm.alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix hp W
      (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) 2 G d₀ hd₀

    have hσmem : ((CuspForm.gammaLift M d₁ : Gamma0 M) : SL(2, ℤ)) ∈ Gamma0 W.R := by
      have h1 := (CuspForm.gammaLift M d₁ : Gamma0 M).2
      rw [Gamma0_mem] at h1 ⊢
      have hdvd : W.R ∣ M := Dvd.intro_left p W.hM.symm
      have h2 := congrArg (ZMod.castHom hdvd (ZMod W.R)) h1
      rw [map_zero, map_intCast] at h2
      exact h2
    have hdvd : W.R ∣ M := Dvd.intro_left p W.hM.symm
    let σ' : Gamma0 W.R := ⟨(CuspForm.gammaLift M d₁ : Gamma0 M), hσmem⟩
    have e1 : ((d₁ : (ZMod M)ˣ) : ZMod M) =
        ((((CuspForm.gammaLift M d₁ : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := by
      conv_lhs => rw [← CuspForm.gamma0Units_gammaLift (M := M) d₁]
      rfl
    have hσ' : CohCarrier.gamma0Units W.R σ' = d₀ := by
      apply Units.ext
      show ((((σ' : Gamma0 W.R) : SL(2, ℤ)) 1 1 : ℤ) : ZMod W.R) = (d₀ : ZMod W.R)
      rw [hd₀def]
      show _ = ZMod.castHom hdvd (ZMod W.R) ((d₁ : (ZMod M)ˣ) : ZMod M)
      rw [e1, map_intCast]
    have hdG : (⇑(CuspForm.diamondLinH 2 d₀ G) : UpperHalfPlane → ℂ) = ⇑(CuspForm.diamondLinH 2 d₁ Gt) := by
      rw [CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD W.R _ 2) d₀ σ' hσ' G,
        CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) d₁ Gt, hGGt]

    set g : UpperHalfPlane → ℂ := fun τ => (CuspForm.diamondLinH 2 d₁ Gt) (ModularForm.heckeDiagMatrix p • τ) with hgdef
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hZ₁' : (⇑Z₁ : UpperHalfPlane → ℂ) = (p : ℂ) • g := by
      funext τ
      rw [hZ₁, show (⇑Gt : UpperHalfPlane → ℂ) = ⇑G from hGGt.symm, hLS,
        ModularForm.slash_heckeDiagMatrix_apply 2 hp.ne_zero, hdG, Pi.smul_apply, smul_eq_mul, hgdef]
      norm_num
    have hg' : g = (p : ℂ)⁻¹ • (⇑Z₁ : UpperHalfPlane → ℂ) := by
      rw [hZ₁', smul_smul, inv_mul_cancel₀ hp0, one_smul]
    have hcoef := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul (CuspForm.diamondLinH 2 d₁ Gt)
      (one_mem_strictPeriods M H) hp.ne_zero n
    change qCoeff g n = _ at hcoef
    rw [hg', qCoeff_smul_coe] at hcoef
    have hZc : qCoeff (⇑Z₁) n = (p : ℂ) * (if p ∣ n then qCoeff (⇑(CuspForm.diamondLinH 2 d₁ Gt)) (n / p) else 0) := by
      rw [← hcoef, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
    rw [hZc]
    refine A.mul_mem (natCast_mem A p) ?_
    split_ifs with hpn
    ·
      have hsplit : CuspForm.diamondLinH 2 d₁ Gt =
          CuspForm.diamondLinH 2 d₁ (CuspForm.diamondLinH 2 d₁ X) +
            CuspForm.heckeULinH 2 p (CuspForm.diamondLinH 2 d₁ (CuspForm.diamondLinH 2 d₁ f)) := by
        rw [hGt, map_add, hYdef, ← hcomm, ← hcomm]
      rw [hsplit, qCoeff_coe_add, CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hp hpM]
      rw [diamondLinH_diamondLinH, diamondLinH_diamondLinH]
      exact A.add_mem ((hXN (d₁ * d₁)) W (n / p)).1 ((hf (d₁ * d₁)) W (n / p * p)).1
    · exact A.zero_mem

theorem naiveS_heckeULinH (hpM2 : ¬ p ^ 2 ∣ M) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (GammaH M H) 2) (hf : NaiveS p A f) : NaiveS p A (CuspForm.heckeULinH 2 q f) := by
  have hp : p.Prime := Fact.out
  have hcommq := (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H 2).2.2.2.1 q hq hqM
  intro d
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨d₁, hd₁⟩ := exists_unit_eq_p (M := M) hpM hpM2

    have e : CuspForm.diamondLinH 2 d (CuspForm.heckeULinH 2 q f) =
        CuspForm.diamondLinH 2 d₁ (CuspForm.heckeULinH 2 q (CuspForm.diamondLinH 2 (d * d₁⁻¹) f)) := by
      rw [hcommq, diamondLinH_diamondLinH, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact naive_diamondLinH_heckeULinH_self hpM hHp d₁ hd₁ _ (hf.diamondLinH (d * d₁⁻¹))
  · rw [← hcommq]
    exact naive_heckeULinH_of_ne' hpM hHp hq hqM hqp _ (hf d)

end Main

end GenUS

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
p2m_export "CuspForm" "smul_apply coe_sub ext coe_add heckeGenH heckeGenH_T heckeGenH_U heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet gammaLift gamma0Units_gammaLift unitOfPrimeNotDvd StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash heckeULinH coe_heckeULinH_apply heckeTLinH qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash alSlash_coe_heckeTLinH_eq_coe_heckeTLinH heckeTLinH_heckeULinH_diamondLinH_comm exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_coe_heckeULinH_eq_coe_heckeULinH qCoeff_heckeULinH_eq_qCoeff_mul exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash alSlash_alSlash_eq_pow_smul_diamondLinH stableU"
namespace WTransportCL
p2m_open "CuspForm"
theorem diamondLinH_mem_heckeRingH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (d : (ZMod M)ˣ) :
    (CuspForm.diamondLinH (H := H) k d) ∈ CuspForm.heckeRingH M H k := by
  have := CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) k (.dia d)
  rwa [CuspForm.heckeGenH_dia] at this
end CuspForm.WTransportCL

namespace CuspForm
p2m_export "CuspForm" "smul_apply coe_sub ext coe_add heckeGenH heckeGenH_T heckeGenH_U heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet gammaLift gamma0Units_gammaLift unitOfPrimeNotDvd StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash heckeULinH coe_heckeULinH_apply heckeTLinH qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash alSlash_coe_heckeTLinH_eq_coe_heckeTLinH heckeTLinH_heckeULinH_diamondLinH_comm exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_coe_heckeULinH_eq_coe_heckeULinH qCoeff_heckeULinH_eq_qCoeff_mul exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash alSlash_alSlash_eq_pow_smul_diamondLinH stableU"
namespace HeckeStabS
p2m_open "CuspForm"

open GenT

def NaiveD (p : ℕ) {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (h : CuspForm (CohCarrier.GammaH M H) 2) : Prop :=
  ∀ (d : (ZMod M)ˣ) (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
    ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d h)) n ∈ (⊥ : Subring ℂ) ∧
      ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 d h)) n ∈ (⊥ : Subring ℂ)

theorem naiveD_heckeTLinH
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hS : NaiveD p f) : NaiveD p (CuspForm.heckeTLinH 2 hℓ hℓM f) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set A : Subring ℂ := ⊥ with hA
  have hℓA : ((ℓ : ℂ) ^ ((2 : ℤ) - 1)) ∈ A := by
    rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
    exact natCast_mem A ℓ

  have hinf : ∀ (g : CuspForm (CohCarrier.GammaH M H) 2),
      (∀ n, ModularFormClass.qCoeff (⇑g) n ∈ A) →
      (∀ n, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 (CuspForm.unitOfPrimeNotDvd hℓ hℓM) g)) n ∈ A) →
      ∀ n, ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH 2 hℓ hℓM g)) n ∈ A := by
    intro g hg hdg n
    rw [CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH M H 2 hℓ hℓM g n]
    refine add_mem (hg _) (mul_mem hℓA ?_)
    split_ifs
    · exact hdg _
    · exact zero_mem A

  intro d W n
  have hcomm := (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H 2).2.2.1 ℓ hℓ hℓM d f
  rw [← hcomm]

  set f₁ : CuspForm (CohCarrier.GammaH M H) 2 := CuspForm.diamondLinH 2 d f with hf₁
  have hS₁ : ∀ (e : (ZMod M)ˣ) (W' : ModularForm.AtkinLehnerDatum M p) (m : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 e f₁)) m ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 e f₁)) m ∈ A := by
    intro e W' m
    rw [hf₁, coe_diamondLinH_diamondLinH 2 d e f]
    exact hS (d * e) W' m
  have hf₁n : ∀ (W' : ModularForm.AtkinLehnerDatum M p) (m : ℕ),
      ModularFormClass.qCoeff (⇑f₁) m ∈ A ∧ ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑f₁) m ∈ A := by
    intro W' m
    have := hS₁ 1 W' m
    rwa [CuspForm.C2W.diamondLinH_one] at this
  refine ⟨hinf f₁ (fun m => (hf₁n W m).1) (fun m => (hS₁ _ W m).1) n, ?_⟩

  have hHp' : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
    have hR : W.R = M / p :=
      (Nat.div_eq_of_eq_mul_left (Fact.out : p.Prime).pos (W.hM.trans (Nat.mul_comm p W.R))).symm
    intro u hu
    exact hHp u ((unitsMap_eq_one_iff_of_eq hR _ _ u).mp hu)
  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash (Fact.out) W H hHp' 2 f₁
  rw [CuspForm.alSlash_coe_heckeTLinH_eq_coe_heckeTLinH M p hpM H hHp W 2 hℓ hℓM f₁ X hX]
  have hY : ∀ (e : (ZMod M)ˣ) (m : ℕ), ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 e X)) m ∈ A := by
    intro e m
    obtain ⟨ds, hdsR, hdsp⟩ := exists_unit_crt M p hpM hpM2 (ZMod.unitsMap hpM e)⁻¹ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)
    obtain ⟨d', hd'R, hd'p, hW⟩ := CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash M p hpM H hHp W 2 ds f₁ X hX
    have hdsp' : ZMod.unitsMap hpM ds = (ZMod.unitsMap hpM e)⁻¹ := by
      apply Units.ext
      simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe]
      exact hdsp
    have hd' : d' = e := by
      apply units_eq_of_unitsMap_eq M p hpM hpM2
      · rw [hd'R, hdsR]
      · rw [map_mul, hdsp'] at hd'p
        exact (mul_inv_eq_one.mp hd'p)
    rw [← hd', ← hW]
    exact (hS₁ ds W m).2
  refine hinf X (fun m => ?_) (hY _) n
  rw [hX]
  exact (hf₁n W m).2

theorem naiveD_diamondLinH (p : ℕ) {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (d₀ : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hS : NaiveD p f) : NaiveD p (CuspForm.diamondLinH 2 d₀ f) := by
  intro d W n
  rw [coe_diamondLinH_diamondLinH 2 d₀ d f]
  exact hS (d₀ * d) W n

end CuspForm.HeckeStabS

namespace CuspForm
p2m_export "CuspForm" "smul_apply coe_sub ext coe_add heckeGenH heckeGenH_T heckeGenH_U heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet gammaLift gamma0Units_gammaLift unitOfPrimeNotDvd StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash heckeULinH coe_heckeULinH_apply heckeTLinH qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash alSlash_coe_heckeTLinH_eq_coe_heckeTLinH heckeTLinH_heckeULinH_diamondLinH_comm exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_coe_heckeULinH_eq_coe_heckeULinH qCoeff_heckeULinH_eq_qCoeff_mul exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash alSlash_alSlash_eq_pow_smul_diamondLinH stableU"
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
p2m_export "CuspForm" "smul_apply coe_sub ext coe_add heckeGenH heckeGenH_T heckeGenH_U heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet gammaLift gamma0Units_gammaLift unitOfPrimeNotDvd StableD diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash heckeULinH coe_heckeULinH_apply heckeTLinH qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH exists_GammaH_coe_eq_alSlash stableD exists_alSlash_diamondLinH_eq_diamondLinH_alSlash alSlash_coe_heckeTLinH_eq_coe_heckeTLinH heckeTLinH_heckeULinH_diamondLinH_comm exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH alSlash_coe_heckeULinH_eq_coe_heckeULinH qCoeff_heckeULinH_eq_qCoeff_mul exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash alSlash_alSlash_eq_pow_smul_diamondLinH stableU"
namespace HeckeStabS
p2m_open "CuspForm"

theorem naiveD_heckeULinH
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hS : NaiveD p f) : NaiveD p (CuspForm.heckeULinH 2 q f) :=
  fun d W n => GenUS.naiveS_heckeULinH hpM hHp hpM2 hq hqM f (fun d W n => hS d W n) d W n

theorem naiveD_heckeGenH
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (g : CohCarrier.Gen M (∅ : Set ℕ)) (h : CuspForm (CohCarrier.GammaH M H) 2) (hS : NaiveD p h) :
    NaiveD p (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2 g h) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      rw [CuspForm.heckeGenH_T]
      exact naiveD_heckeTLinH p M hpM hpM2 H hHp hℓ hℓM h hS
  | U q hq hqM =>
      rw [CuspForm.heckeGenH_U]
      exact naiveD_heckeULinH p M hpM hpM2 H hHp hq hqM h hS
  | dia d =>
      rw [CuspForm.heckeGenH_dia]
      exact naiveD_diamondLinH p d h hS

end CuspForm.HeckeStabS

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (g : CohCarrier.Gen M (∅ : Set ℕ))
    (h : CuspForm (CohCarrier.GammaH M H) 2)
    (hS : ∀ (d : (ZMod M)ˣ) (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
        ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d h)) n ∈ (⊥ : Subring ℂ) ∧
          ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 d h)) n ∈ (⊥ : Subring ℂ)) :
    ∀ (d : (ZMod M)ˣ) (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
        ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2 g h))) n ∈ (⊥ : Subring ℂ) ∧
          ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 d (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2 g h))) n ∈ (⊥ : Subring ℂ) :=
  CuspForm.HeckeStabS.naiveD_heckeGenH p M hpM hpM2 H hHp g h hS

end S_CuspForm_forall_qCoeff_diamondLinH_heckeGenH_mem_of_forall_qCoeff_diamondLinH_mem
end P2MW
export P2MW.S_CuspForm_forall_qCoeff_diamondLinH_heckeGenH_mem_of_forall_qCoeff_diamondLinH_mem (solution)
