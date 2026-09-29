-- Prove2me | solution 1 for CuspForm.forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/62c5e0c3-d043-5dfb-a3e8-fa3b9b76daa6

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_CuspForm_alSlash_coe_heckeULinH_eq_coe_heckeULinH
import Theorems.Thm_ModularForm_alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix
import Theorems.Thm_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
import Theorems.Thm_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_diamondLinH_add_smul_heckeU_alSlash
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_alSlash_alSlash_eq_pow_smul_diamondLinH
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups ModularForm

namespace GenU

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

end GenU

namespace GenU

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
  (hdia : ∀ (d : (ZMod M)ˣ) (g : CuspForm (GammaH M H) 2), Naive p A g → Naive p A (CuspForm.diamondLinH 2 d g))
include hpM hHp hdia

theorem exists_X (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (GammaH M H) 2) (hf : Naive p A f) :
    ∃ X : CuspForm (GammaH M H) 2, ⇑X = ModularForm.alSlash W 2 ⇑f ∧ Naive p A X := by
  have hp : p.Prime := Fact.out
  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H (hHp_R hpM hHp W) 2 f
  refine ⟨X, hX, fun W' n => ⟨?_, ?_⟩⟩
  · rw [hX]; exact (hf W n).2
  · obtain ⟨δ, hδ⟩ := CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH M p hpM H hHp W' W 2 f
    have h1 : ((p : ℂ) ^ ((2 : ℤ) - 2)) = 1 := by norm_num
    rw [hX, hδ, h1, one_smul]
    exact ((hdia δ f hf) W' n).1

omit hdia in

theorem naive_heckeULinH_of_ne {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (GammaH M H) 2) (hf : Naive p A f) : Naive p A (CuspForm.heckeULinH 2 q f) := by
  have hp : p.Prime := Fact.out
  intro W n
  refine ⟨?_, ?_⟩
  · rw [CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hq hqM]; exact (hf W (n * q)).1
  · obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H (hHp_R hpM hHp W) 2 f
    rw [CuspForm.alSlash_coe_heckeULinH_eq_coe_heckeULinH M p hpM H hHp W 2 hq hqM hqp f X hX,
      CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hq hqM, hX]
    exact (hf W (n * q)).2

include hpM2 in

theorem naive_heckeULinH_self (f : CuspForm (GammaH M H) 2) (hf : Naive p A f) :
    Naive p A (CuspForm.heckeULinH 2 p f) := by
  have hp : p.Prime := Fact.out
  have hcomm := (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm M H 2).2.2.2.1 p hp hpM
  obtain ⟨d₁, hd₁⟩ := exists_unit_eq_p (M := M) hpM hpM2

  set Y : CuspForm (GammaH M H) 2 := CuspForm.diamondLinH 2 d₁ (CuspForm.heckeULinH 2 p f) with hYdef
  suffices hY : Naive p A Y by
    have : CuspForm.heckeULinH 2 p f = CuspForm.diamondLinH 2 d₁⁻¹ Y := by
      rw [hYdef, diamondLinH_inv_diamondLinH]
    rw [this]; exact hdia _ Y hY
  have hYcomm : Y = CuspForm.heckeULinH 2 p (CuspForm.diamondLinH 2 d₁ f) := by rw [hYdef, hcomm]
  intro W n
  refine ⟨?_, ?_⟩
  ·
    rw [hYcomm, CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H 2 hp hpM]
    exact ((hdia d₁ f hf) W (n * p)).1
  ·
    haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
    obtain ⟨X, hX, hXN⟩ := exists_X hpM hHp hdia W f hf
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
    · rw [hZ₂]; exact ((hdia d₁ X hXN) W n).2

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
      exact A.add_mem ((hdia d₁ _ (hdia d₁ X hXN)) W (n / p)).1 ((hdia d₁ _ (hdia d₁ f hf)) W (n / p * p)).1
    · exact A.zero_mem

end Main

end GenU

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : Subring ℂ)
    (hdia : ∀ (d : (ZMod M)ˣ) (g : CuspForm (CohCarrier.GammaH M H) 2),
      (∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(g)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(g)) n ∈ A) →
      ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d g)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 d g)) n ∈ A)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(f)) n ∈ A) :
    ∀ (W : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.heckeULinH 2 q f)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.heckeULinH 2 q f)) n ∈ A := by
  by_cases hqp : q = p
  · subst hqp
    exact GenU.naive_heckeULinH_self hpM hpM2 hHp (A := A) hdia f hf
  · exact GenU.naive_heckeULinH_of_ne hpM hHp (A := A) hq hqM hqp f hf

end S_CuspForm_forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem
end P2MW
export P2MW.S_CuspForm_forall_qCoeff_heckeULinH_mem_of_forall_qCoeff_diamondLinH_mem (solution)
