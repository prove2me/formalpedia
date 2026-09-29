-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f5ddb4a5-3fbf-5740-9d3d-d95c94ee0307

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_comp_of_X_pow_mem_span
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_X_pow_mem_span_comp_of_comp_eq_id
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_map_eq_of_frobenius_eq_verschiebungInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants_zero
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

noncomputable section
namespace We82BR

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]

section generic
variable {d : ℕ} {Φ Φ' : MvFormalGroup d R} [Φ.IsComm] [Φ'.IsComm]

theorem curve_map (φ : Φ.Hom Φ') (f : CartierModule p Φ) (k : Fin d) :
    curve (CartierModule.map φ f) k = subst (curve f) (φ.toPowerSeries k) := by
  rw [curve_apply, toPowerSeries_map, subst_comp_subst_apply f.hasSubst_toPowerSeries hasSubst_curveFam]
  rfl

theorem curve_endAct (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) (k : Fin d) :
    curve (endAct φ f) k = subst (curve f) (φ.toPowerSeries k) := by
  rw [endAct_apply]
  exact curve_map φ f k

theorem curve_teichmuller_smul (a : R) (f : CartierModule p Φ) (k : Fin d) :
    curve (WittVector.teichmuller p a • f) k = PowerSeries.rescale a (curve f k) := by
  rw [teichmuller_smul, curve_homothety]

end generic

section branch

theorem witt_branch (j : Zp2 p →+* R) (ξ : R) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ 0)) :
    endAct X.varpiEnd (γ 0) = verschiebungInt (γ 0) ∧
    endAct X.varpiEnd (γ 1) =
      (WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0 + verschiebungInt (γ 1) := by
  have h := FormalODModule.endAct_varpiEnd_eq_teichmuller_sub_smul_add_verschiebungInt_of_hasStructureConstants_edgeConstants
    p j ξ 0 (mul_zero ξ) X γ hγ ha
  obtain ⟨h0, h1⟩ := h
  refine ⟨?_, h1⟩
  rw [h0, zero_pow (Fact.out : p.Prime).ne_zero, sub_self, zero_smul, zero_add]

theorem frobenius_eq_verschiebungInt_branch (j : Zp2 p →+* R) (ξ : R) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ 0)) :
    frobenius (γ 0) = verschiebungInt (γ 0) := by
  have h0 := (witt_branch j ξ X γ hγ ha).1
  have key : verschiebungInt (frobenius (γ 0)) = verschiebungInt (verschiebungInt (γ 0)) := by
    rw [verschiebungInt_apply_eq_verschiebung (frobenius (γ 0)), verschiebung_frobenius_eq_smul,
      natCast_smul_eq_nsmul', ← FormalODModule.endAct_varpiEnd_endAct_varpiEnd X (γ 0), h0,
      endAct_verschiebungInt, h0]
  have hinj : Function.Injective (verschiebungInt : CartierModule p X.F → CartierModule p X.F) := by
    rw [verschiebungInt_eq_verschiebung]
    exact verschiebung_injective
  exact hinj key

theorem subst_curve_varpi_zero (j : Zp2 p →+* R) (ξ : R) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ 0)) (k : Fin 2) :
    subst (curve (γ 0)) (X.varpi k) = PowerSeries.expand p (Fact.out : p.Prime).ne_zero (curve (γ 0) k) := by
  have h0 := (witt_branch j ξ X γ hγ ha).1
  have := congrArg (fun f => curve f k) h0
  rw [curve_endAct, curve_verschiebungInt] at this
  exact this

theorem subst_curve_varpi_one (j : Zp2 p →+* R) (ξ : R) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ 0)) (k : Fin 2) :
    subst (curve (γ 1)) (X.varpi k) =
      subst (Sum.elim (curve ((WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0))
        (fun l => PowerSeries.expand p (Fact.out : p.Prime).ne_zero (curve (γ 1) l))) (X.F.toPowerSeries k) := by
  have h1 := (witt_branch j ξ X γ hγ ha).2
  have := congrArg (fun f => curve f k) h1
  rw [curve_endAct, curve_add, show X.varpiEnd.toPowerSeries k = X.varpi k from rfl] at this
  rw [this]
  congr 1
  funext l
  rcases l with l | l
  · rfl
  · exact curve_verschiebungInt _ _

theorem curve_teichmuller_sub_smul (X : FormalODModule p R) (a b : R) (f : CartierModule p X.F) (k : Fin 2) :
    curve ((WittVector.teichmuller p a - WittVector.teichmuller p b) • f) k =
      subst (Sum.elim (fun l => PowerSeries.rescale a (curve f l)) (curve (-(WittVector.teichmuller p b • f))))
        (X.F.toPowerSeries k) := by
  rw [sub_smul, sub_eq_add_neg, curve_add]
  congr 1
  funext l
  rcases l with l | l
  · exact curve_teichmuller_smul a f l
  · rfl

end branch

end We82BR
end

noncomputable section
namespace We84Chart

open MvPowerSeries

variable {R : Type} [CommRing R]

private def _root_.We84Chart.emb (i : Fin 2) (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) f

p2m_export "We84Chart" "emb"
theorem hasSubst_emb (i : Fin 2) : HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) :=
  hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_X i)

theorem emb_def (i : Fin 2) (f : PowerSeries R) :
    emb i f = subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) f := rfl

private theorem _root_.We84Chart.constantCoeff_emb (i : Fin 2) (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (emb i f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_emb i) (fun _ => constantCoeff_X i) hf

p2m_export "We84Chart" "constantCoeff_emb"

theorem emb_subst (i : Fin 2) {τ : Type} [Finite τ] (c : τ → PowerSeries R) (hc : ∀ l, PowerSeries.constantCoeff (c l) = 0)
    (g : MvPowerSeries τ R) : emb i (subst c g) = subst (fun l => emb i (c l)) g := by
  rw [emb_def, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hc) (hasSubst_emb i)]
  rfl

def cfam (c₀ c₁ : Fin 2 → PowerSeries R) : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2) R :=
  Sum.elim (fun l => emb 0 (c₀ l)) (fun l => emb 1 (c₁ l))

theorem constantCoeff_cfam (c₀ c₁ : Fin 2 → PowerSeries R)
    (h₀ : ∀ l, PowerSeries.constantCoeff (c₀ l) = 0) (h₁ : ∀ l, PowerSeries.constantCoeff (c₁ l) = 0) :
    ∀ s, constantCoeff (cfam c₀ c₁ s) = 0 := by
  rintro (l | l)
  · exact constantCoeff_emb 0 _ (h₀ l)
  · exact constantCoeff_emb 1 _ (h₁ l)

def chart (Φ : MvFormalGroup 2 R) (c₀ c₁ : Fin 2 → PowerSeries R) : Series R :=
  fun i => subst (cfam c₀ c₁) (Φ.toPowerSeries i)

theorem chart_apply (Φ : MvFormalGroup 2 R) (c₀ c₁ : Fin 2 → PowerSeries R) (i : Fin 2) :
    chart Φ c₀ c₁ i = subst (Sum.elim (fun l => emb 0 (c₀ l)) (fun l => emb 1 (c₁ l))) (Φ.toPowerSeries i) := rfl

section
variable (Φ : MvFormalGroup 2 R) (c₀ c₁ : Fin 2 → PowerSeries R)
  (h₀ : ∀ l, PowerSeries.constantCoeff (c₀ l) = 0) (h₁ : ∀ l, PowerSeries.constantCoeff (c₁ l) = 0)
include h₀ h₁

theorem hasSubst_cfam : HasSubst (cfam c₀ c₁) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_cfam c₀ c₁ h₀ h₁)

theorem constantCoeff_chart (i : Fin 2) : constantCoeff (chart Φ c₀ c₁ i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_cfam c₀ c₁ h₀ h₁) (constantCoeff_cfam c₀ c₁ h₀ h₁) (Φ.constantCoeff_eq_zero i)

theorem comp_chart_eq_chart (π : Series R) (hπ : SpecialFormal.IsLawHom Φ Φ π) :
    π.comp (chart Φ c₀ c₁) = chart Φ (fun l => subst c₀ (π l)) (fun l => subst c₁ (π l)) := by
  have hF : HasSubst Φ.toPowerSeries := hasSubst_of_constantCoeff_zero Φ.constantCoeff_eq_zero
  have hinl : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) :=
    hasSubst_of_constantCoeff_zero (fun l => constantCoeff_X _)
  have hinr : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) :=
    hasSubst_of_constantCoeff_zero (fun l => constantCoeff_X _)
  have hE : HasSubst (Sum.elim
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) (π j))
      (fun j => subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) R)) (π j))) :=
    hasSubst_of_constantCoeff_zero (by
      rintro (l | l)
      · exact constantCoeff_subst_eq_zero hinl (fun _ => constantCoeff_X _) (hπ.1 l)
      · exact constantCoeff_subst_eq_zero hinr (fun _ => constantCoeff_X _) (hπ.1 l))
  have hc := hasSubst_cfam c₀ c₁ h₀ h₁
  funext i
  have h := congrArg (subst (cfam c₀ c₁)) (hπ.2 i)
  rw [subst_comp_subst_apply hF hc, subst_comp_subst_apply hE hc] at h
  refine h.trans ?_
  show _ = subst _ _
  congr 1
  funext s
  rcases s with l | l
  · show subst (cfam c₀ c₁) (subst _ (π l)) = emb 0 (subst c₀ (π l))
    rw [subst_comp_subst_apply hinl hc, emb_subst 0 c₀ h₀]
    congr 1
    funext m
    rw [subst_X hc]
    rfl
  · show subst (cfam c₀ c₁) (subst _ (π l)) = emb 1 (subst c₁ (π l))
    rw [subst_comp_subst_apply hinr hc, emb_subst 1 c₁ h₁]
    congr 1
    funext m
    rw [subst_X hc]
    rfl

end

section branch
variable {p : ℕ} [Fact p.Prime] [CharP R p]

theorem varpi_comp_chart_branch (j : Zp2 p →+* R) (ξ : R) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ 0)) :
    X.varpi.comp (chart X.F (curve (γ 0)) (curve (γ 1))) =
      chart X.F
        (fun l => PowerSeries.expand p (Fact.out : p.Prime).ne_zero (curve (γ 0) l))
        (fun l => subst
            (Sum.elim (curve ((WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ) • γ 0))
              (fun m => PowerSeries.expand p (Fact.out : p.Prime).ne_zero (curve (γ 1) m)))
            (X.F.toPowerSeries l)) := by
  rw [comp_chart_eq_chart X.F (curve (γ 0)) (curve (γ 1)) (constantCoeff_curve (γ 0)) (constantCoeff_curve (γ 1))
    X.varpi X.isLawHom_varpi]
  congr 1
  · funext l; exact We82BR.subst_curve_varpi_zero j ξ X γ hγ ha l
  · funext l; exact We82BR.subst_curve_varpi_one j ξ X γ hγ ha l

end branch

end We84Chart

namespace We84Chart
open MvPowerSeries

variable {R : Type} [CommRing R] {d : ℕ}

def lin {τ : Type} (M : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries τ R) : Fin d → MvPowerSeries τ R :=
  fun i => ∑ j, M i j • a j

theorem lin_apply {τ : Type} (M : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries τ R) (i : Fin d) :
    lin M a i = ∑ j, M i j • a j := rfl

theorem lin_lin {τ : Type} (M N : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries τ R) :
    lin M (lin N a) = lin (M * N) a := by
  funext i
  simp only [lin_apply, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem lin_one {τ : Type} (a : Fin d → MvPowerSeries τ R) : lin 1 a = a := by
  funext i
  simp [lin_apply, Matrix.one_apply]

theorem coeff_lin {τ : Type} (M : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries τ R) (i : Fin d) (n : τ →₀ ℕ) :
    coeff n (lin M a i) = ∑ j, M i j * coeff n (a j) := by
  simp only [lin_apply, map_sum, map_smul, smul_eq_mul]

theorem constantCoeff_lin {τ : Type} (M : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries τ R)
    (ha : ∀ j, constantCoeff (a j) = 0) (i : Fin d) : constantCoeff (lin M a i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_lin]
  simp only [coeff_zero_eq_constantCoeff_apply, ha, mul_zero, Finset.sum_const_zero]

theorem linearPart_lin (M : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries (Fin d) R) :
    MvFormalGroup.linearPart (lin M a) = M * MvFormalGroup.linearPart a := by
  ext i k
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.mul_apply, coeff_lin]

theorem subst_lin {τ τ' : Type} (M : Matrix (Fin d) (Fin d) R) (a : Fin d → MvPowerSeries τ R)
    (b : τ → MvPowerSeries τ' R) (hb : HasSubst b) (i : Fin d) :
    subst b (lin M a i) = lin M (fun j => subst b (a j)) i := by
  simp only [lin_apply, ← coe_substAlgHom hb, map_sum, map_smul]

theorem linearPart_X : MvFormalGroup.linearPart (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) = 1 := by
  ext i k
  simp only [MvFormalGroup.linearPart, Matrix.of_apply, coeff_X, Matrix.one_apply]
  by_cases h : i = k
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro hk
    exact h (Finsupp.single_left_injective one_ne_zero hk).symm

theorem exists_subst_eq_X_of_isUnit_det_linearPart (u : Fin d → MvPowerSeries (Fin d) R)
    (hu0 : ∀ i, constantCoeff (u i) = 0) (hT : IsUnit (MvFormalGroup.linearPart u).det) :
    ∃ v : Fin d → MvPowerSeries (Fin d) R,
      (∀ i, constantCoeff (v i) = 0) ∧ (∀ i, subst v (u i) = X i) ∧ (∀ i, subst u (v i) = X i) := by
  classical
  obtain ⟨inv⟩ : Nonempty (Invertible (MvFormalGroup.linearPart u)) := ⟨Matrix.invertibleOfIsUnitDet _ hT⟩
  set T := MvFormalGroup.linearPart u with hTdef
  set w : Fin d → MvPowerSeries (Fin d) R := lin (⅟T) u with hw
  have hw0 : ∀ i, constantCoeff (w i) = 0 := constantCoeff_lin _ _ hu0
  have hw1 : MvFormalGroup.linearPart w = 1 := by rw [hw, linearPart_lin, invOf_mul_self]
  obtain ⟨ψ, hψ0, hψw, hwψ⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one w hw0 hw1
  set L : Fin d → MvPowerSeries (Fin d) R := lin (⅟T) (fun i => X i) with hL
  have hL0 : ∀ i, constantCoeff (L i) = 0 := constantCoeff_lin _ _ (fun j => constantCoeff_X j)
  have hLs : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  have hus : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun i => subst L (ψ i), fun i => constantCoeff_subst_eq_zero hLs hL0 (hψ0 i), fun i => ?_, fun i => ?_⟩
  ·
    have hvs : HasSubst (fun i => subst L (ψ i)) :=
      hasSubst_of_constantCoeff_zero (fun i => constantCoeff_subst_eq_zero hLs hL0 (hψ0 i))
    have huw : u = lin T w := by rw [hw, lin_lin, mul_invOf_self, lin_one]
    have hvw : ∀ j, subst (fun i => subst L (ψ i)) (w j) = L j := by
      intro j
      rw [← subst_comp_subst_apply hψs hLs, hwψ j, subst_X hLs]
    rw [huw, subst_lin _ _ _ hvs]
    simp only [hvw]
    rw [hL, lin_lin, mul_invOf_self, lin_one]
  ·
    rw [subst_comp_subst_apply hLs hus]
    have : (fun j => subst u (L j)) = w := by
      funext j
      rw [hL, subst_lin _ _ _ hus, hw]
      congr 1
      funext k
      exact subst_X hus k
    rw [this, hψw i]

theorem exists_subst_chart_eq_X (Φ : MvFormalGroup 2 R) (c₀ c₁ : Fin 2 → PowerSeries R)
    (h₀ : ∀ l, PowerSeries.constantCoeff (c₀ l) = 0) (h₁ : ∀ l, PowerSeries.constantCoeff (c₁ l) = 0)
    (hT : IsUnit (MvFormalGroup.linearPart (chart Φ c₀ c₁)).det) :
    ∃ v : Series R,
      (∀ i, constantCoeff (v i) = 0) ∧ (∀ i, subst v (chart Φ c₀ c₁ i) = X i) ∧ (∀ i, subst (chart Φ c₀ c₁) (v i) = X i) :=
  exists_subst_eq_X_of_isUnit_det_linearPart _ (constantCoeff_chart Φ c₀ c₁ h₀ h₁) hT

end We84Chart

namespace We84Chart
open MvPowerSeries

variable {R : Type} [CommRing R]

theorem coeff_single_emb (j k : Fin 2) (f : PowerSeries R) :
    coeff (Finsupp.single k 1) (emb j f) = if k = j then PowerSeries.coeff 1 f else 0 := by
  classical
  rw [emb_def, MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X j)]
  simp only [Finset.univ_unique, Finset.sum_singleton, coeff_X, Finsupp.single_left_inj one_ne_zero]
  by_cases h : k = j
  · rw [if_pos h, if_pos h, mul_one]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

theorem linearPart_chart (Φ : MvFormalGroup 2 R) (c₀ c₁ : Fin 2 → PowerSeries R)
    (h₀ : ∀ l, PowerSeries.constantCoeff (c₀ l) = 0) (h₁ : ∀ l, PowerSeries.constantCoeff (c₁ l) = 0) :
    MvFormalGroup.linearPart (chart Φ c₀ c₁) =
      Matrix.of fun i k : Fin 2 => if k = 0 then PowerSeries.coeff 1 (c₀ i) else PowerSeries.coeff 1 (c₁ i) := by
  classical
  ext i k
  rw [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.of_apply]
  show coeff (Finsupp.single k 1) (subst (cfam c₀ c₁) (Φ.toPowerSeries i)) = _
  rw [MvFormalGroup.coeff_single_subst (constantCoeff_cfam c₀ c₁ h₀ h₁), Fintype.sum_sum_type]
  simp only [cfam, Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, coeff_single_emb,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  fin_cases k
  · simp
  · simp

variable {p : ℕ} [Fact p.Prime]

theorem linearPart_chart_curve (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F) :
    MvFormalGroup.linearPart (chart X.F (curve (γ 0)) (curve (γ 1))) =
      (Matrix.of fun i k : Fin 2 => tangent (γ i) k).transpose := by
  rw [linearPart_chart _ _ _ (constantCoeff_curve _) (constantCoeff_curve _)]
  ext i k
  fin_cases k
  · simp [Matrix.transpose_apply, coeff_one_curve]
  · simp [Matrix.transpose_apply, coeff_one_curve]

theorem isUnit_det_linearPart_chart_curve (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ2 : IsUnit (Matrix.of fun i k : Fin 2 => tangent (γ i) k).det) :
    IsUnit (MvFormalGroup.linearPart (chart X.F (curve (γ 0)) (curve (γ 1)))).det := by
  rw [linearPart_chart_curve, Matrix.det_transpose]
  exact hγ2

theorem exists_subst_chart_curve_eq_X (X : FormalODModule p R) (j : Zp2 p →+* R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) :
    ∃ v : Series R, (∀ i, constantCoeff (v i) = 0) ∧
      (∀ i, subst v (chart X.F (curve (γ 0)) (curve (γ 1)) i) = MvPowerSeries.X i) ∧
      (∀ i, subst (chart X.F (curve (γ 0)) (curve (γ 1))) (v i) = MvPowerSeries.X i) :=
  exists_subst_chart_eq_X X.F _ _ (constantCoeff_curve _) (constantCoeff_curve _)
    (isUnit_det_linearPart_chart_curve X γ hγ.2)

end We84Chart

end

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace We83Tail

variable {R : Type} [CommRing R]

theorem add_pow_sub_pow_mem {A : Type u} [CommRing A] (I : Ideal A) {a b : A} (ha : a ∈ I) (n : ℕ) :
    (a + b) ^ n - b ^ n ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, map_add,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, sub_self]

theorem X_pow_mul_mem (q n : ℕ) (M : MvPowerSeries (Fin 2) R)
    (hM : M - MvPowerSeries.X 0 ^ q ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R))) :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ (q * n) ∈
      Ideal.span ({M} : Set (MvPowerSeries (Fin 2) R)) ⊔ Ideal.span {MvPowerSeries.X 1 ^ n} := by
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hM

  have hx : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ q = M + (-g) * MvPowerSeries.X 1 := by
    linear_combination hg
  rw [pow_mul, hx]
  have h1 : (M + -g * MvPowerSeries.X 1) ^ n - (-g * MvPowerSeries.X 1) ^ n ∈
      Ideal.span ({M} : Set (MvPowerSeries (Fin 2) R)) :=
    add_pow_sub_pow_mem _ (Ideal.mem_span_singleton_self M) n
  have h2 : (-g * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ n ∈
      Ideal.span ({MvPowerSeries.X 1 ^ n} : Set (MvPowerSeries (Fin 2) R)) := by
    rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have := Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
  rwa [sub_add_cancel] at this

theorem exists_X_pow_mem_span_of_node (q : ℕ) (hq : 1 ≤ q) (Q : Series R)
    (h0 : Q 0 - MvPowerSeries.X 0 ^ q ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)))
    (h1 : Q 1 = MvPowerSeries.X 1 ^ q) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range Q) := by
  have hle : Ideal.span ({Q 0} : Set (MvPowerSeries (Fin 2) R)) ⊔ Ideal.span {MvPowerSeries.X 1 ^ q} ≤
      Ideal.span (Set.range Q) := by
    refine sup_le ?_ ?_ <;> rw [Ideal.span_le, Set.singleton_subset_iff]
    · exact Ideal.subset_span ⟨0, rfl⟩
    · rw [← h1]; exact Ideal.subset_span ⟨1, rfl⟩
  refine ⟨q * q, fun i => ?_⟩
  fin_cases i
  · exact hle (X_pow_mul_mem q q (Q 0) h0)
  · have : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ (q * q) ∈
        Ideal.span ({MvPowerSeries.X 1 ^ q} : Set (MvPowerSeries (Fin 2) R)) := by
      rw [pow_mul]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) q hq
    exact hle (Ideal.mem_sup_right this)

theorem subst_mem_span {φ : Series R} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (g : MvPowerSeries (Fin 2) R) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst φ g ∈ Ideal.span (Set.range φ) := by
  have hX : g ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) R)) := by
    have h1 := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 g (fun m hm => by
      have hm0 : m = 0 := by
        rw [Nat.lt_one_iff] at hm
        exact (Finsupp.degree_eq_zero_iff m).mp hm
      subst hm0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hg)
    rwa [pow_one] at h1
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have h := Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom ha).toRingHom hX
  rw [Ideal.map_span] at h
  rw [← MvPowerSeries.coe_substAlgHom ha]
  refine (Ideal.span_mono ?_) h
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨j, ?_⟩
  show φ j = MvPowerSeries.substAlgHom ha (MvPowerSeries.X j)
  rw [MvPowerSeries.substAlgHom_X]

theorem span_le_span_comp (u v Q : Series R)
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (hvu : v.comp u = Series.id R) :
    Ideal.span (Set.range Q) ≤ Ideal.span (Set.range (u.comp Q)) := by
  have hcomp : (v.comp u).comp Q = v.comp (u.comp Q) := Series.comp_assoc v u Q hu0 hQ0
  have hid : (Series.id R).comp Q = Q := Series.id_comp Q hQ0
  have huQ0 : ∀ i, MvPowerSeries.constantCoeff ((u.comp Q) i) = 0 :=
    fun i => Series.constantCoeff_comp hu0 hQ0 i
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hi : Q i = MvPowerSeries.subst (u.comp Q) (v i) := by
    have := congrFun hcomp i
    rw [hvu, hid] at this
    exact this
  rw [hi]
  exact subst_mem_span huQ0 (v i) (hv0 i)

theorem exists_X_pow_mem_span_act {p : ℕ} [Fact p.Prime] (X : FormalODModule p R)
    (u v : Series R)
    (hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0)
    (huv : u.comp v = Series.id R) (hvu : v.comp u = Series.id R)
    (Q : Series R) (hQ0 : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (hkey : X.varpi.comp u = u.comp Q)
    (hmem : ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range Q)) :
    ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range (X.act (p : Zp2 p))) := by

  have hle := span_le_span_comp u v Q hu0 hv0 hQ0 hvu
  have hmem' : ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range (X.varpi.comp u)) := by
    obtain ⟨N, hN⟩ := hmem
    exact ⟨N, fun i => by rw [hkey]; exact hle (hN i)⟩

  have hvarpi : ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range X.varpi) :=
    CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_X_pow_mem_span_comp_of_comp_eq_id
      hu0 hv0 huv hmem'

  rw [← X.varpi_comp_varpi]
  exact CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_comp_of_X_pow_mem_span
    X.isLawHom_varpi.1 hvarpi hvarpi

theorem subst_sub_mem_span_X_one (m : MvPowerSeries (Fin 2) R)
    (hm0 : m - MvPowerSeries.X 0 ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)))
    (τ : Fin 2 → MvPowerSeries (Fin 2) R) (hτ0 : ∀ i, MvPowerSeries.constantCoeff (τ i) = 0)
    (hτ1 : τ 1 ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R))) :
    MvPowerSeries.subst τ m - τ 0 ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)) := by
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hm0
  have ha := MvPowerSeries.hasSubst_of_constantCoeff_zero hτ0
  set S := MvPowerSeries.substAlgHom (R := R) ha with hS
  have hSm : S m = MvPowerSeries.subst τ m := by rw [hS, MvPowerSeries.coe_substAlgHom]
  have hSX : ∀ i, S (MvPowerSeries.X i) = τ i := fun i => by rw [hS, MvPowerSeries.substAlgHom_X]
  have key : MvPowerSeries.subst τ m - τ 0 = S g * τ 1 := by
    rw [← hSm, ← hSX 0, ← hSX 1, ← map_mul, ← map_sub, hg]
  rw [key]
  exact Ideal.mul_mem_left _ _ hτ1

theorem subst_powerSeries_mem_span_X_one (r : PowerSeries R) (hr : PowerSeries.constantCoeff r = 0) :
    MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) r ∈
      Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)) := by

  have hX : (r : MvPowerSeries Unit R) ∈
      Ideal.span (Set.range (MvPowerSeries.X : Unit → MvPowerSeries Unit R)) := by
    have h1 := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 (r : MvPowerSeries Unit R) (fun m hm => by
      have hm0 : m = 0 := by
        rw [Nat.lt_one_iff] at hm
        exact (Finsupp.degree_eq_zero_iff m).mp hm
      subst hm0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hr)
    rwa [pow_one] at h1
  have h0 : ∀ _ : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) ()) = 0 :=
    fun _ => MvPowerSeries.constantCoeff_X _
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have h := Ideal.mem_map_of_mem (MvPowerSeries.substAlgHom ha).toRingHom hX
  rw [Ideal.map_span] at h
  rw [← MvPowerSeries.coe_substAlgHom ha]
  refine (Ideal.span_mono ?_) h
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  show MvPowerSeries.substAlgHom ha (MvPowerSeries.X u) ∈ ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R))
  rw [MvPowerSeries.substAlgHom_X]
  exact Set.mem_singleton _

end We83Tail

open MvFormalGroup MvFormalGroup.CartierModule MvPowerSeries

noncomputable section
namespace We82AC

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

theorem curve_eq_const {H : MvFormalGroup 1 R} (ε : CartierModule p H) : curve ε = fun _ => curve ε 0 := by
  funext j
  rw [Fin.fin_one_eq_zero j]

theorem curve_map' {d d' : ℕ} {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]
    (φ : Φ.Hom Φ') (f : CartierModule p Φ) (k : Fin d') :
    curve (CartierModule.map φ f) k = subst (curve f) (φ.toPowerSeries k) := by
  rw [curve_apply, toPowerSeries_map, subst_comp_subst_apply f.hasSubst_toPowerSeries hasSubst_curveFam]
  rfl

theorem hsU {τ : Type*} {a : MvPowerSeries τ R} (ha : constantCoeff a = 0) : HasSubst (fun _ : Unit => a) :=
  hasSubst_of_constantCoeff_zero fun _ => ha

theorem hs1 {τ : Type*} {a : MvPowerSeries τ R} (ha : constantCoeff a = 0) : HasSubst (fun _ : Fin 1 => a) :=
  hasSubst_of_constantCoeff_zero fun _ => ha

theorem subst_const_subst_const {τ : Type*} (f : PowerSeries R) (b : PowerSeries R) (a : MvPowerSeries τ R)
    (hb : PowerSeries.constantCoeff b = 0) (ha : constantCoeff a = 0) :
    subst (fun _ : Unit => a) (subst (fun _ : Unit => b) f) = subst (fun _ : Unit => subst (fun _ : Unit => a) b) f :=
  subst_comp_subst_apply (hsU hb) (hsU ha) f

theorem exists_comp_inverse (e : PowerSeries R) (he0 : PowerSeries.constantCoeff e = 0)
    (he1 : IsUnit (PowerSeries.coeff 1 e)) :
    ∃ einv : PowerSeries R, PowerSeries.constantCoeff einv = 0 ∧
      subst (fun _ : Unit => einv) e = (X () : PowerSeries R) ∧ subst (fun _ : Unit => e) einv = (X () : PowerSeries R) := by
  refine ⟨e.substInvOfIsUnit he1, PowerSeries.constantCoeff_substInvOfIsUnit e he1, ?_, ?_⟩
  · have := PowerSeries.subst_substInvOfIsUnit_right e he0 he1
    rw [PowerSeries.subst_def] at this
    exact this
  · have := PowerSeries.subst_substInvOfIsUnit_left e he0 he1
    rw [PowerSeries.subst_def] at this
    exact this

theorem cancel_of_inverse {τ : Type*} {e einv : PowerSeries R} (heinv0 : PowerSeries.constantCoeff einv = 0)
    (hR : subst (fun _ : Unit => einv) e = (X () : PowerSeries R)) (g : MvPowerSeries τ R) (hg : constantCoeff g = 0) :
    subst (fun _ : Unit => subst (fun _ : Unit => g) einv) e = g := by
  rw [← subst_const_subst_const e einv g heinv0 hg, hR, subst_X (hsU hg)]

theorem subst_zero_of_constantCoeff {τ : Type*} (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) :
    subst (fun _ : Unit => (0 : MvPowerSeries τ R)) f = 0 := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hf
  have h0 : HasSubst (fun _ : Unit => (0 : MvPowerSeries τ R)) := hasSubst_of_constantCoeff_zero fun _ => map_zero _
  rw [hg, ← coe_substAlgHom h0, map_mul, coe_substAlgHom, show (PowerSeries.X : PowerSeries R) = X () from rfl,
    subst_X h0, zero_mul]

section main

variable (Φ : MvFormalGroup 2 R) [Φ.IsComm] (H : MvFormalGroup 1 R) [H.IsComm]
  (ε : CartierModule p H) (φ : H.Hom Φ) (γ₀ : CartierModule p Φ)

def embA (e : PowerSeries R) (k : Fin 2) : Fin 1 → MvPowerSeries (Fin 2) R :=
  fun _ => subst (fun _ : Unit => (X k : MvPowerSeries (Fin 2) R)) e

theorem embA_const0 (e : PowerSeries R) (he0 : PowerSeries.constantCoeff e = 0) (k : Fin 2) (j : Fin 1) :
    constantCoeff (embA e k j) = 0 :=
  constantCoeff_subst_eq_zero (hsU (constantCoeff_X _)) (fun _ => constantCoeff_X _) he0

theorem subst_curve_gamma {τ : Type*} (hγ : CartierModule.map φ ε = γ₀) {a : MvPowerSeries τ R}
    (ha : constantCoeff a = 0) (l : Fin 2) :
    subst (fun _ : Unit => a) (curve γ₀ l) =
      subst (fun _ : Fin 1 => subst (fun _ : Unit => a) (curve ε 0)) (φ.toPowerSeries l) := by
  rw [← hγ, curve_map', curve_eq_const,
    subst_comp_subst_apply (hs1 (constantCoeff_curve ε 0)) (hsU ha)]

theorem axis_curve (hε : IsUnit (CartierModule.tangent ε 0)) (hγ : CartierModule.map φ ε = γ₀) :
    (∃ m : MvPowerSeries (Fin 2) R, constantCoeff m = 0 ∧
        subst ![(X 0 : MvPowerSeries (Fin 2) R), 0] m = X 0 ∧
        ∀ i : Fin 2,
          subst (Sum.elim (fun l => subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (curve γ₀ l))
              (fun l => subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (curve γ₀ l)))
            (Φ.toPowerSeries i) =
          subst (fun _ : Unit => m) (curve γ₀ i)) ∧
    (∀ w : WittVector p R, ∃ r : PowerSeries R, PowerSeries.constantCoeff r = 0 ∧
        ∀ l : Fin 2, curve (w • γ₀) l = subst (fun _ : Unit => r) (curve γ₀ l)) := by
  have he0 : PowerSeries.constantCoeff (curve ε 0) = 0 := constantCoeff_curve ε 0
  have he1 : IsUnit (PowerSeries.coeff 1 (curve ε 0)) := by rw [coeff_one_curve]; exact hε
  obtain ⟨einv, heinv0, hR, hL⟩ := exists_comp_inverse (curve ε 0) he0 he1
  refine ⟨?_, ?_⟩
  ·
    have ha := embA_const0 (curve ε 0) he0 0
    have hb := embA_const0 (curve ε 0) he0 1
    have hHst0 : constantCoeff (subst (Sum.elim (embA (curve ε 0) 0) (embA (curve ε 0) 1)) (H.toPowerSeries 0)) = 0 :=
      constantCoeff_subst_eq_zero (hasSubst_elim ha hb) (by rintro (j | j); exacts [ha j, hb j]) (H.constantCoeff_eq_zero 0)
    refine ⟨subst (fun _ : Unit => subst (Sum.elim (embA (curve ε 0) 0) (embA (curve ε 0) 1)) (H.toPowerSeries 0)) einv,
      ?_, ?_, ?_⟩
    · exact constantCoeff_subst_eq_zero (hsU hHst0) (fun _ => hHst0) heinv0
    ·
      have hX : HasSubst (![(X 0 : MvPowerSeries (Fin 2) R), 0] : Fin 2 → MvPowerSeries (Fin 2) R) :=
        hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [constantCoeff_X])
      rw [subst_comp_subst_apply (hsU hHst0) hX]
      have h1 : subst ![(X 0 : MvPowerSeries (Fin 2) R), 0]
          (subst (Sum.elim (embA (curve ε 0) 0) (embA (curve ε 0) 1)) (H.toPowerSeries 0)) = embA (curve ε 0) 0 0 := by
        rw [subst_comp_subst_apply (hasSubst_elim ha hb) hX]
        have hfam : (fun s : Fin 1 ⊕ Fin 1 =>
            subst ![(X 0 : MvPowerSeries (Fin 2) R), 0] (Sum.elim (embA (curve ε 0) 0) (embA (curve ε 0) 1) s)) =
            Sum.elim (embA (curve ε 0) 0) (fun _ => 0) := by
          funext s
          rcases s with j | j
          · show subst ![(X 0 : MvPowerSeries (Fin 2) R), 0]
                (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (curve ε 0)) = embA (curve ε 0) 0 j
            rw [subst_comp_subst_apply (hsU (constantCoeff_X _)) hX]
            show subst (fun _ : Unit => subst ![(X 0 : MvPowerSeries (Fin 2) R), 0] (X 0)) (curve ε 0) = _
            rw [subst_X hX]
            rfl
          · show subst ![(X 0 : MvPowerSeries (Fin 2) R), 0]
                (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (curve ε 0)) = 0
            rw [subst_comp_subst_apply (hsU (constantCoeff_X _)) hX]
            have : (fun _ : Unit => subst ![(X 0 : MvPowerSeries (Fin 2) R), 0] (X 1 : MvPowerSeries (Fin 2) R)) =
                fun _ : Unit => (0 : MvPowerSeries (Fin 2) R) := by
              funext; rw [subst_X hX]; rfl
            rw [this]
            exact subst_zero_of_constantCoeff _ he0
        rw [hfam]
        exact H.subst_elim_zero_right ha 0
      rw [show (fun _ : Unit => subst ![(X 0 : MvPowerSeries (Fin 2) R), 0]
          (subst (Sum.elim (embA (curve ε 0) 0) (embA (curve ε 0) 1)) (H.toPowerSeries 0))) =
          fun _ : Unit => embA (curve ε 0) 0 0 from funext fun _ => h1]
      show subst (fun _ : Unit => subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (curve ε 0)) einv = X 0
      rw [← subst_const_subst_const einv (curve ε 0) (X 0) he0 (constantCoeff_X _), hL,
        subst_X (hsU (constantCoeff_X _))]
    · intro i

      rw [subst_curve_gamma Φ H ε φ γ₀ hγ (constantCoeff_subst_eq_zero (hsU hHst0) (fun _ => hHst0) heinv0),
        cancel_of_inverse heinv0 hR _ hHst0]

      have hl0 : (fun l => subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) (curve γ₀ l)) =
          fun l => subst (embA (curve ε 0) 0) (φ.toPowerSeries l) :=
        funext fun l => subst_curve_gamma Φ H ε φ γ₀ hγ (constantCoeff_X _) l
      have hl1 : (fun l => subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (curve γ₀ l)) =
          fun l => subst (embA (curve ε 0) 1) (φ.toPowerSeries l) :=
        funext fun l => subst_curve_gamma Φ H ε φ γ₀ hγ (constantCoeff_X _) l
      rw [hl0, hl1, ← MvFormalGroup.Hom.subst_subst_elim φ ha hb i]
      congr 1
      funext j
      rw [Fin.fin_one_eq_zero j]
  ·
    intro w
    have hg0 : PowerSeries.constantCoeff (curve (w • ε) 0) = 0 := constantCoeff_curve _ 0
    refine ⟨subst (fun _ : Unit => curve (w • ε) 0) einv, ?_, ?_⟩
    · exact constantCoeff_subst_eq_zero (hsU hg0) (fun _ => hg0) heinv0
    · intro l
      have hsm : w • γ₀ = CartierModule.map φ (w • ε) := by rw [map_smul_witt, hγ]
      rw [subst_curve_gamma Φ H ε φ γ₀ hγ (constantCoeff_subst_eq_zero (hsU hg0) (fun _ => hg0) heinv0),
        cancel_of_inverse heinv0 hR _ hg0, hsm, curve_map', curve_eq_const (w • ε)]

end main
end We82AC
end

open MvPowerSeries

namespace We81Splice

variable {R : Type u} [CommRing R]

noncomputable def eval2 (Φ : MvFormalGroup 2 R) {σ : Type} (A B : Fin 2 → MvPowerSeries σ R) :
    Fin 2 → MvPowerSeries σ R :=
  fun i => subst (Sum.elim A B) (Φ.toPowerSeries i)

theorem constantCoeff_elim {σ : Type} {A B : Fin 2 → MvPowerSeries σ R}
    (hA : ∀ l, constantCoeff (A l) = 0) (hB : ∀ l, constantCoeff (B l) = 0) :
    ∀ s, constantCoeff (Sum.elim A B s) = 0 := by
  rintro (l | l)
  · exact hA l
  · exact hB l

theorem hasSubst_elim {σ : Type} {A B : Fin 2 → MvPowerSeries σ R}
    (hA : ∀ l, constantCoeff (A l) = 0) (hB : ∀ l, constantCoeff (B l) = 0) :
    HasSubst (Sum.elim A B) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_elim hA hB)

theorem constantCoeff_eval2 (Φ : MvFormalGroup 2 R) {σ : Type} {A B : Fin 2 → MvPowerSeries σ R}
    (hA : ∀ l, constantCoeff (A l) = 0) (hB : ∀ l, constantCoeff (B l) = 0) (i : Fin 2) :
    constantCoeff (eval2 Φ A B i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim hA hB) (constantCoeff_elim hA hB) (Φ.constantCoeff_eq_zero i)

theorem subst_eval2 (Φ : MvFormalGroup 2 R) {σ σ' : Type} [Finite σ] {A B : Fin 2 → MvPowerSeries σ R}
    (hA : ∀ l, constantCoeff (A l) = 0) (hB : ∀ l, constantCoeff (B l) = 0)
    {τ : σ → MvPowerSeries σ' R} (hτ : HasSubst τ) (i : Fin 2) :
    subst τ (eval2 Φ A B i) = eval2 Φ (fun l => subst τ (A l)) (fun l => subst τ (B l)) i := by
  show subst τ (subst (Sum.elim A B) (Φ.toPowerSeries i)) = subst _ (Φ.toPowerSeries i)
  rw [subst_comp_subst_apply (hasSubst_elim hA hB) hτ]
  congr 1
  funext s
  rcases s with l | l <;> rfl

theorem eval2_assoc (Φ : MvFormalGroup 2 R) {σ : Type} [Finite σ] {A B C : Fin 2 → MvPowerSeries σ R}
    (hA : ∀ l, constantCoeff (A l) = 0) (hB : ∀ l, constantCoeff (B l) = 0)
    (hC : ∀ l, constantCoeff (C l) = 0) (i : Fin 2) :
    eval2 Φ (eval2 Φ A B) C i = eval2 Φ A (eval2 Φ B C) i := by

  have hBC : ∀ l, constantCoeff (eval2 Φ B C l) = 0 := constantCoeff_eval2 Φ hB hC
  have hAB : ∀ l, constantCoeff (eval2 Φ A B l) = 0 := constantCoeff_eval2 Φ hA hB
  set τ : Fin 2 ⊕ (Fin 2 ⊕ Fin 2) → MvPowerSeries σ R := Sum.elim A (Sum.elim B C) with hτ
  have hτ0 : ∀ s, constantCoeff (τ s) = 0 := by
    rintro (l | l | l)
    · exact hA l
    · exact hB l
    · exact hC l
  have hτs : HasSubst τ := hasSubst_of_constantCoeff_zero hτ0
  have key := congrArg (subst τ) (Φ.assoc i)

  have hXl : HasSubst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
      fun l => X (Sum.inr (Sum.inl l))) :=
    hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
  have hXr : HasSubst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
      fun l => X (Sum.inr (Sum.inr l))) :=
    hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> exact constantCoeff_X _)
  have hL : HasSubst (Sum.elim
      (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
        fun l => X (Sum.inr (Sum.inl l))) (Φ.toPowerSeries j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hXl (by rintro (l | l) <;> exact constantCoeff_X _) (Φ.constantCoeff_eq_zero j)
    · exact constantCoeff_X _
  have hR' : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
      fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
        fun l => X (Sum.inr (Sum.inr l))) (Φ.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_X _
    · exact constantCoeff_subst_eq_zero hXr (by rintro (l | l) <;> exact constantCoeff_X _) (Φ.constantCoeff_eq_zero j)
  rw [subst_comp_subst_apply hL hτs, subst_comp_subst_apply hR' hτs] at key

  have e1 : (fun s => subst τ ((Sum.elim
      (fun j => subst (Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
        fun l => X (Sum.inr (Sum.inl l))) (Φ.toPowerSeries j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R)) s)) =
      Sum.elim (eval2 Φ A B) C := by
    funext s
    rcases s with j | j
    · show subst τ (subst _ (Φ.toPowerSeries j)) = subst (Sum.elim A B) (Φ.toPowerSeries j)
      rw [subst_comp_subst_apply hXl hτs]
      congr 1
      funext s'
      rcases s' with l | l
      · show subst τ (X (Sum.inl l)) = A l
        rw [subst_X hτs]; rfl
      · show subst τ (X (Sum.inr (Sum.inl l))) = B l
        rw [subst_X hτs]; rfl
    · show subst τ (X (Sum.inr (Sum.inr j))) = C j
      rw [subst_X hτs]; rfl
  have e2 : (fun s => subst τ ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
      fun j => subst (Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) R))
        fun l => X (Sum.inr (Sum.inr l))) (Φ.toPowerSeries j)) s)) =
      Sum.elim A (eval2 Φ B C) := by
    funext s
    rcases s with j | j
    · show subst τ (X (Sum.inl j)) = A j
      rw [subst_X hτs]; rfl
    · show subst τ (subst _ (Φ.toPowerSeries j)) = subst (Sum.elim B C) (Φ.toPowerSeries j)
      rw [subst_comp_subst_apply hXr hτs]
      congr 1
      funext s'
      rcases s' with l | l
      · show subst τ (X (Sum.inr (Sum.inl l))) = B l
        rw [subst_X hτs]; rfl
      · show subst τ (X (Sum.inr (Sum.inr l))) = C l
        rw [subst_X hτs]; rfl
  rw [e1, e2] at key
  exact key

noncomputable def emb (i : Fin 2) (f : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) f

noncomputable def ev {σ : Type} (P : MvPowerSeries σ R) (f : PowerSeries R) : MvPowerSeries σ R :=
  subst (fun _ : Unit => P) f

theorem hasSubst_const {σ : Type} {P : MvPowerSeries σ R} (hP : constantCoeff P = 0) :
    HasSubst (fun _ : Unit => P) :=
  hasSubst_of_constantCoeff_zero (fun _ => hP)

theorem constantCoeff_ev {σ : Type} {P : MvPowerSeries σ R} (hP : constantCoeff P = 0) {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (ev P f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_const hP) (fun _ => hP) hf

theorem emb_eq_ev (i : Fin 2) (f : PowerSeries R) : emb i f = ev (X i : MvPowerSeries (Fin 2) R) f := rfl

theorem constantCoeff_emb (i : Fin 2) {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    constantCoeff (emb i f) = 0 :=
  constantCoeff_ev (constantCoeff_X _) hf

theorem subst_ev {σ σ' : Type} [Finite σ] {P : MvPowerSeries σ R} (hP : constantCoeff P = 0)
    {τ : σ → MvPowerSeries σ' R} (hτ : HasSubst τ) (f : PowerSeries R) :
    subst τ (ev P f) = ev (subst τ P) f := by
  show subst τ (subst (fun _ : Unit => P) f) = subst (fun _ : Unit => subst τ P) f
  rw [subst_comp_subst_apply (hasSubst_const hP) hτ]

theorem subst_emb {σ' : Type} (i : Fin 2) {τ : Fin 2 → MvPowerSeries σ' R} (hτ : HasSubst τ) (f : PowerSeries R) :
    subst τ (emb i f) = ev (τ i) f := by
  rw [emb_eq_ev, subst_ev (constantCoeff_X _) hτ, subst_X hτ]

theorem emb_expand (i : Fin 2) (q : ℕ) (hq : q ≠ 0) (f : PowerSeries R) :
    emb i (PowerSeries.expand q hq f) = ev ((X i : MvPowerSeries (Fin 2) R) ^ q) f := by
  rw [PowerSeries.expand_apply]
  show subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R))
      (subst (fun _ : Unit => (PowerSeries.X : PowerSeries R) ^ q) f) = _
  have hXq : HasSubst (fun _ : Unit => (PowerSeries.X : PowerSeries R) ^ q) :=
    hasSubst_of_constantCoeff_zero (fun _ => by
      rw [map_pow, show constantCoeff (PowerSeries.X : PowerSeries R) = 0 from PowerSeries.constantCoeff_X, zero_pow hq])
  have hh : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) := hasSubst_const (constantCoeff_X i)
  rw [subst_comp_subst_apply hXq hh]
  congr 1
  funext u
  rw [← coe_substAlgHom hh, map_pow, coe_substAlgHom hh]
  congr 1
  exact subst_X hh ()

private noncomputable def _root_.We81Splice.chart (Φ : MvFormalGroup 2 R) (c₀ c₁ : Fin 2 → PowerSeries R) : Fin 2 → MvPowerSeries (Fin 2) R :=
  eval2 Φ (fun l => emb 0 (c₀ l)) (fun l => emb 1 (c₁ l))

p2m_export "We81Splice" "chart"

theorem splice (Φ : MvFormalGroup 2 R) (c₀ c₁ d : Fin 2 → PowerSeries R)
    (h₀ : ∀ l, PowerSeries.constantCoeff (c₀ l) = 0) (h₁ : ∀ l, PowerSeries.constantCoeff (c₁ l) = 0)
    (hd : ∀ l, PowerSeries.constantCoeff (d l) = 0)
    (q : ℕ) (hq : q ≠ 0)
    (m : MvPowerSeries (Fin 2) R) (hm : constantCoeff m = 0)
    (hM : ∀ i, eval2 Φ (fun l => emb 0 (c₀ l)) (fun l => emb 1 (c₀ l)) i = ev m (c₀ i))
    (r : PowerSeries R) (hr : PowerSeries.constantCoeff r = 0)
    (hW : ∀ l, d l = subst (fun _ : Unit => r) (c₀ l)) :
    chart Φ (fun l => PowerSeries.expand q hq (c₀ l))
        (fun l => subst (Sum.elim d (fun k => PowerSeries.expand q hq (c₁ k))) (Φ.toPowerSeries l)) =
      fun i => subst (![subst ![(X 0 : MvPowerSeries (Fin 2) R) ^ q, emb 1 r] m, (X 1 : MvPowerSeries (Fin 2) R) ^ q])
        (chart Φ c₀ c₁ i) := by
  classical

  have hX0q : constantCoeff ((X 0 : MvPowerSeries (Fin 2) R) ^ q) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have hX1q : constantCoeff ((X 1 : MvPowerSeries (Fin 2) R) ^ q) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have hr1 : constantCoeff (emb 1 r) = 0 := constantCoeff_emb 1 hr
  set τ : Fin 2 → MvPowerSeries (Fin 2) R := ![(X 0 : MvPowerSeries (Fin 2) R) ^ q, emb 1 r] with hτ
  have hτ0 : ∀ i, constantCoeff (τ i) = 0 := by
    intro i; fin_cases i
    · exact hX0q
    · exact hr1
  have hτs : HasSubst τ := hasSubst_of_constantCoeff_zero hτ0
  have hmτ : constantCoeff (subst τ m) = 0 := constantCoeff_subst_eq_zero hτs hτ0 hm
  set Q : Fin 2 → MvPowerSeries (Fin 2) R := ![subst τ m, (X 1 : MvPowerSeries (Fin 2) R) ^ q] with hQ
  have hQ0 : ∀ i, constantCoeff (Q i) = 0 := by
    intro i; fin_cases i
    · exact hmτ
    · exact hX1q
  have hQs : HasSubst Q := hasSubst_of_constantCoeff_zero hQ0

  have hA : ∀ l, constantCoeff (ev ((X 0 : MvPowerSeries (Fin 2) R) ^ q) (c₀ l)) = 0 :=
    fun l => constantCoeff_ev hX0q (h₀ l)
  have hB : ∀ l, constantCoeff (ev (emb 1 r) (c₀ l)) = 0 := fun l => constantCoeff_ev hr1 (h₀ l)
  have hC : ∀ l, constantCoeff (ev ((X 1 : MvPowerSeries (Fin 2) R) ^ q) (c₁ l)) = 0 :=
    fun l => constantCoeff_ev hX1q (h₁ l)
  have hE0 : ∀ l, constantCoeff (emb 0 (c₀ l)) = 0 := fun l => constantCoeff_emb 0 (h₀ l)
  have hE1 : ∀ l, constantCoeff (emb 1 (c₀ l)) = 0 := fun l => constantCoeff_emb 1 (h₀ l)
  have hE1' : ∀ l, constantCoeff (emb 1 (c₁ l)) = 0 := fun l => constantCoeff_emb 1 (h₁ l)

  have hdc : HasSubst (Sum.elim d fun k => PowerSeries.expand q hq (c₁ k)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (l | l)
    · exact hd l
    · show PowerSeries.constantCoeff (PowerSeries.expand q hq (c₁ l)) = 0
      rw [PowerSeries.constantCoeff_expand]; exact h₁ l
  have lhs : chart Φ (fun l => PowerSeries.expand q hq (c₀ l))
      (fun l => subst (Sum.elim d (fun k => PowerSeries.expand q hq (c₁ k))) (Φ.toPowerSeries l)) =
      eval2 Φ (fun l => ev ((X 0 : MvPowerSeries (Fin 2) R) ^ q) (c₀ l))
        (eval2 Φ (fun l => ev (emb 1 r) (c₀ l)) (fun l => ev ((X 1 : MvPowerSeries (Fin 2) R) ^ q) (c₁ l))) := by
    funext i
    show eval2 Φ _ _ i = eval2 Φ _ _ i
    congr 1
    · funext l; exact emb_expand 0 q hq (c₀ l)
    · funext l
      show subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (subst _ (Φ.toPowerSeries l)) = _
      rw [subst_comp_subst_apply hdc (hasSubst_const (constantCoeff_X _))]
      show subst _ (Φ.toPowerSeries l) = subst _ (Φ.toPowerSeries l)
      congr 1
      funext s
      rcases s with k | k
      · show subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (d k) = ev (emb 1 r) (c₀ k)
        rw [hW k, subst_comp_subst_apply (hasSubst_const hr) (hasSubst_const (constantCoeff_X _))]
        rfl
      · show subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (PowerSeries.expand q hq (c₁ k)) = _
        exact emb_expand 1 q hq (c₁ k)

  have axis : eval2 Φ (fun l => ev ((X 0 : MvPowerSeries (Fin 2) R) ^ q) (c₀ l)) (fun l => ev (emb 1 r) (c₀ l)) =
      fun i => ev (subst τ m) (c₀ i) := by
    funext i
    have h := congrArg (subst τ) (hM i)
    rw [subst_eval2 Φ hE0 hE1 hτs, subst_ev hm hτs] at h
    have e0 : (fun l => subst τ (emb 0 (c₀ l))) = fun l => ev ((X 0 : MvPowerSeries (Fin 2) R) ^ q) (c₀ l) := by
      funext l; rw [subst_emb 0 hτs]; rfl
    have e1 : (fun l => subst τ (emb 1 (c₀ l))) = fun l => ev (emb 1 r) (c₀ l) := by
      funext l; rw [subst_emb 1 hτs]; rfl
    rw [e0, e1] at h
    exact h

  rw [lhs]
  funext i
  rw [← eval2_assoc Φ hA hB hC i, axis]
  show eval2 Φ _ _ i = subst Q (eval2 Φ (fun l => emb 0 (c₀ l)) (fun l => emb 1 (c₁ l)) i)
  rw [subst_eval2 Φ hE0 hE1' hQs]
  congr 1
  · funext l; rw [subst_emb 0 hQs]; rfl
  · funext l; rw [subst_emb 1 hQs]; rfl

end We81Splice

namespace We84L
open MvPowerSeries

variable {R : Type*} [CommRing R]

theorem hasSubst_axis : HasSubst (![(X 0 : MvPowerSeries (Fin 2) R), 0] : Fin 2 → MvPowerSeries (Fin 2) R) :=
  hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)

theorem coeff_subst_axis (f : MvPowerSeries (Fin 2) R) (m : Fin 2 →₀ ℕ) (hm : m 1 = 0) :
    coeff m (subst ![(X 0 : MvPowerSeries (Fin 2) R), 0] f) = coeff m f := by
  classical
  have hsingle : ∀ d : Fin 2 →₀ ℕ, d 1 = 0 → d = Finsupp.single 0 (d 0) := by
    intro d hd
    ext i
    fin_cases i
    · simp
    · simp [hd]
  rw [coeff_subst hasSubst_axis, finsum_eq_single _ m]
  · rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hm, pow_zero, mul_one,
      coeff_X_pow]
    rw [if_pos ((hsingle m hm).trans rfl), smul_eq_mul, mul_one]
  · intro d hd
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h1 : d 1 = 0
    · rw [h1, pow_zero, mul_one, coeff_X_pow, if_neg, smul_zero]
      intro hmd
      exact hd ((hsingle d h1).trans hmd.symm)
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]

theorem sub_subst_axis_mem_span (f : MvPowerSeries (Fin 2) R) :
    f - subst ![(X 0 : MvPowerSeries (Fin 2) R), 0] f ∈ Ideal.span ({X 1} : Set (MvPowerSeries (Fin 2) R)) := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]
  intro m hm
  rw [map_sub, coeff_subst_axis f m hm, sub_self]

end We84L

namespace We81Asm

@[reducible] noncomputable def algebraPadicInt {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]
    (j : CerednikDrinfeld.Zp2 p →+* B) : Algebra (PadicInt p) B :=
  (j.comp ((WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp
    (WittVector.equiv p).symm.toRingHom)).toAlgebra

end We81Asm

open MvPowerSeries in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ : R)
    (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ 0)) :
    ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range (X.act (p : Zp2 p))) := by
  classical
  letI : Algebra (PadicInt p) R := We81Asm.algebraPadicInt j
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero

  set c₀ : Fin 2 → PowerSeries R := curve (γ 0) with hc₀
  set c₁ : Fin 2 → PowerSeries R := curve (γ 1) with hc₁
  have h₀ : ∀ l, PowerSeries.constantCoeff (c₀ l) = 0 := fun l => constantCoeff_curve _ l
  have h₁ : ∀ l, PowerSeries.constantCoeff (c₁ l) = 0 := fun l => constantCoeff_curve _ l
  set u : Series R := We84Chart.chart X.F c₀ c₁ with hu
  have hu0 : ∀ i, constantCoeff (u i) = 0 := fun i => We84Chart.constantCoeff_chart X.F c₀ c₁ h₀ h₁ i
  obtain ⟨v, hv0, huv, hvu⟩ := We84Chart.exists_subst_chart_curve_eq_X X j γ hγ

  have hsplit := We84Chart.varpi_comp_chart_branch j ξ X γ hγ ha

  have hFV := We82BR.frobenius_eq_verschiebungInt_branch j ξ X γ hγ ha
  obtain ⟨H, hH, ε, φ, hε, hφ⟩ :=
    MvFormalGroup.CartierModule.exists_hom_map_eq_of_frobenius_eq_verschiebungInt p X.F (γ 0) hFV

  set w : WittVector p R := WittVector.teichmuller p (ξ ^ p) - WittVector.teichmuller p ξ with hw
  obtain ⟨⟨m, hm, hm0s, hM⟩, hWall⟩ := We82AC.axis_curve X.F H ε φ (γ 0) hε hφ
  obtain ⟨r, hr, hW⟩ := hWall w

  have L : ∀ f : MvPowerSeries (Fin 2) R,
      f - MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] f ∈
        Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)) :=
    fun f => We84L.sub_subst_axis_mem_span f
  have hm0 : m - MvPowerSeries.X 0 ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)) := by
    have := L m
    rwa [hm0s] at this

  have hd : ∀ l, PowerSeries.constantCoeff (curve (w • γ 0) l) = 0 := fun l => constantCoeff_curve _ l
  have key := We81Splice.splice X.F c₀ c₁ (curve (w • γ 0)) h₀ h₁ hd p hp0 m hm hM r hr hW
  set Q : Series R := ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ p, We81Splice.emb 1 r] m,
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ p] with hQ
  have hkey : X.varpi.comp u = u.comp Q := by
    rw [hu, hsplit]
    exact key

  have hr1 : constantCoeff (We81Splice.emb 1 r) = 0 := We81Splice.constantCoeff_emb 1 hr
  have hX0p : constantCoeff ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ p) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hp0]
  have hX1p : constantCoeff ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ p) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hp0]
  have hτ0 : ∀ i, constantCoeff ((![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) ^ p, We81Splice.emb 1 r] : Fin 2 → _) i) = 0 := by
    intro i; fin_cases i
    · exact hX0p
    · exact hr1
  have hQ0 : ∀ i, constantCoeff (Q i) = 0 := by
    intro i; fin_cases i
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hτ0) hτ0 hm
    · exact hX1p
  have hB2 : We81Splice.emb 1 r ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)) :=
    We83Tail.subst_powerSeries_mem_span_X_one r hr
  have h0 : Q 0 - MvPowerSeries.X 0 ^ p ∈ Ideal.span ({MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) R)) :=
    We83Tail.subst_sub_mem_span_X_one m hm0 _ hτ0 hB2
  have h1 : Q 1 = MvPowerSeries.X 1 ^ p := rfl
  have hmem := We83Tail.exists_X_pow_mem_span_of_node p hp.one_lt.le Q h0 h1
  exact We83Tail.exists_X_pow_mem_span_act X u v hu0 hv0 (funext huv) (funext hvu) Q hQ0 hkey hmem

end S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants_zero (solution)
