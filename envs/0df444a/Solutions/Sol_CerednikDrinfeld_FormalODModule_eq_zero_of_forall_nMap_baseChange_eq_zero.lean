-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.eq_zero_of_forall_nMap_baseChange_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2d85470f-6d66-5c18-a174-8665aa618c4e

import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecialCartierModule_toGradedCartierModuleData
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace NInj

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem nMk_eq_nMk_iff (D : GradedCartierModuleData p B j) (a b a' b' : D.M) :
    D.nMk (a, b) = D.nMk (a', b') ↔ ∃ t : D.M, D.verschiebung t = a - a' ∧ D.varpi t = b' - b := by
  rw [nMk_apply, nMk_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change (a, D.toSigma b) - (a', D.toSigma b') ∈ LinearMap.range D.nRelMap ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    rw [nRelMap_apply, Prod.mk_sub_mk, Prod.mk.injEq] at hs
    refine ⟨D.ofSigma s, hs.1, ?_⟩
    have h2 : -D.varpi (D.ofSigma s) = b - b' := by
      have := congrArg D.ofSigma hs.2
      simpa using this
    rw [← neg_neg (D.varpi (D.ofSigma s)), h2, neg_sub]
  · rintro ⟨t, ht1, ht2⟩
    refine ⟨D.toSigma t, ?_⟩
    rw [nRelMap_apply, Prod.mk_sub_mk, Prod.mk.injEq]
    refine ⟨by simpa using ht1, ?_⟩
    have : D.ofSigma (D.toSigma t) = t := rfl
    rw [this, ht2, neg_sub]
    rfl

end NInj

theorem solution
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    {ι : Type} (K : ι → Type) [∀ α, CommRing (K α)] (φ : ∀ α, S →+* K α)
    (hinj : ∀ s : S, (∀ α, φ α s = 0) → s = 0)
    (hcK : ∀ α, IsCompl ((X.map (φ α)).gradedPiece ((φ α).comp j) 0) ((X.map (φ α)).gradedPiece ((φ α).comp j) 1))
    (bc : ∀ α, CartierModule p X.F →+ CartierModule p (X.map (φ α)).F)
    (hbc : ∀ α, bc α = CartierModule.baseChange (φ α))
    (hbcV : ∀ α x, bc α ((X.toGradedCartierModuleData j hc).verschiebung x) = ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).verschiebung (bc α x))
    (hbcPi : ∀ α x, bc α ((X.toGradedCartierModuleData j hc).varpi x) = ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).varpi (bc α x))
    (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : ∀ α, (X.toGradedCartierModuleData j hc).nMap ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)) (bc α) (hbcV α) (hbcPi α) z = 0) :
    z = 0 := by
  classical
  obtain ⟨hγD, hDsp⟩ :=
    CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p j X γ hγ hc
  have hγK : ∀ α, ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).IsHomogeneousVBasis (fun i => bc α (γ i)) := by
    intro α
    have h1 := CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.map (φ α) hγ
    have h2 := (CerednikDrinfeld.FormalODModule.isSpecialCartierModule_toGradedCartierModuleData p ((φ α).comp j)
      (X.map (φ α)) _ h1 (hcK α)).1
    rw [hbc α]
    exact h2

  have hγK' : ∀ α (x : (MvFormalGroup.CartierModule p (X.map (φ α)).F)), ∃! cy : (Fin 2 → K α) × (MvFormalGroup.CartierModule p (X.map (φ α)).F),
      x = (∑ i, WittVector.teichmuller p (cy.1 i) • bc α (γ i)) + MvFormalGroup.CartierModule.verschiebungInt cy.2 :=
    fun α => (hγK α).2
  have hbcV' : ∀ α (x : MvFormalGroup.CartierModule p X.F),
      bc α (MvFormalGroup.CartierModule.verschiebungInt x) = MvFormalGroup.CartierModule.verschiebungInt (bc α x) :=
    fun α x => hbcV α x
  have hbcPi' : ∀ α (x : MvFormalGroup.CartierModule p X.F),
      bc α (MvFormalGroup.CartierModule.endAct X.varpiEnd x) = MvFormalGroup.CartierModule.endAct (X.map (φ α)).varpiEnd (bc α x) :=
    fun α x => hbcPi α x
  have hbcT : ∀ α (c : S) (m : MvFormalGroup.CartierModule p X.F),
      bc α (WittVector.teichmuller p c • m) = WittVector.teichmuller p (φ α c) • bc α m := by
    intro α c m
    have key := MvFormalGroup.CartierModule.baseChangeEq_smul_witt (p := p) (φ α)
      (rfl : X.F.map (φ α) = (X.map (φ α)).F) (WittVector.teichmuller p c) m
    rw [WittVector.map_teichmuller] at key
    rw [hbc α]
    exact key
  have huniqK : ∀ α (d d' : Fin 2 → K α) (y y' : (MvFormalGroup.CartierModule p (X.map (φ α)).F)),
      (∑ i, WittVector.teichmuller p (d i) • bc α (γ i)) + MvFormalGroup.CartierModule.verschiebungInt y =
        (∑ i, WittVector.teichmuller p (d' i) • bc α (γ i)) + MvFormalGroup.CartierModule.verschiebungInt y' →
      d = d' ∧ y = y' := by
    intro α d d' y y' h
    obtain ⟨cy, -, huniq⟩ := hγK' α ((∑ i, WittVector.teichmuller p (d i) • bc α (γ i)) + MvFormalGroup.CartierModule.verschiebungInt y)
    have e := (huniq (d, y) rfl).trans (huniq (d', y') h).symm
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

  have peel : ∀ (t : (X.toGradedCartierModuleData j hc).M) (u : ∀ α, (MvFormalGroup.CartierModule p (X.map (φ α)).F)),
      (∀ α, bc α t = MvFormalGroup.CartierModule.verschiebungInt (u α)) →
      ∃ t' : (X.toGradedCartierModuleData j hc).M, t = (X.toGradedCartierModuleData j hc).verschiebung t' ∧ ∀ α, bc α t' = u α := by
    intro t u ht
    obtain ⟨⟨c, t'⟩, hct, -⟩ := hγD.2 t
    have hct' : t = (∑ i, WittVector.teichmuller p (c i) • γ i) + MvFormalGroup.CartierModule.verschiebungInt t' := hct
    have key : ∀ α, (∀ i, φ α (c i) = 0) ∧ bc α t' = u α := by
      intro α
      have h := congrArg (bc α) hct'
      rw [ht α, map_add, map_sum] at h
      simp only [hbcT, hbcV'] at h
      have h' : (∑ i, WittVector.teichmuller p ((fun _ : Fin 2 => (0 : K α)) i) • bc α (γ i)) +
            MvFormalGroup.CartierModule.verschiebungInt (u α) =
          (∑ i, WittVector.teichmuller p (φ α (c i)) • bc α (γ i)) + MvFormalGroup.CartierModule.verschiebungInt (bc α t') := by
        simpa only [WittVector.teichmuller_zero, zero_smul, Finset.sum_const_zero, zero_add] using h
      obtain ⟨hd, hy⟩ := huniqK α _ _ _ _ h'
      exact ⟨fun i => (congrFun hd i).symm, hy.symm⟩
    have hc0 : c = fun _ => 0 := funext fun i => hinj (c i) (fun α => (key α).1 i)
    refine ⟨t', ?_, fun α => (key α).2⟩
    show t = MvFormalGroup.CartierModule.verschiebungInt t'
    rw [hct', hc0]
    simp only [WittVector.teichmuller_zero, zero_smul, Finset.sum_const_zero, zero_add]

  have inj : ∀ x : (X.toGradedCartierModuleData j hc).M, (∀ α, bc α x = 0) → x = 0 := by
    intro x hx
    have hiter : ∀ N : ℕ, ∃ t, (∀ α, bc α t = 0) ∧ x = (⇑(X.toGradedCartierModuleData j hc).verschiebung)^[N] t := by
      intro N
      induction N with
      | zero => exact ⟨x, hx, rfl⟩
      | succ N ih =>
        obtain ⟨t, ht, hxt⟩ := ih
        obtain ⟨t', htt', ht'⟩ := peel t (fun α => 0) (fun α => by rw [ht α, map_zero])
        exact ⟨t', ht', by rw [hxt, htt', ← Function.iterate_succ_apply]⟩
    obtain ⟨s, -, huniq⟩ := hDsp.2 (fun _ => 0)
    have h0 : (0 : (X.toGradedCartierModuleData j hc).M) = s := huniq 0 (fun N => ⟨0, by simp⟩)
    have hx' : x = s := huniq x (fun N => by
      obtain ⟨t, -, hxt⟩ := hiter N
      exact ⟨t, by simpa using hxt⟩)
    rw [hx', ← h0]

  obtain ⟨⟨a, b⟩, rfl⟩ := (X.toGradedCartierModuleData j hc).nMk_surjective z
  have hz' : ∀ α, ∃ mα : (MvFormalGroup.CartierModule p (X.map (φ α)).F), bc α a = MvFormalGroup.CartierModule.verschiebungInt mα ∧
      bc α b = -MvFormalGroup.CartierModule.endAct (X.map (φ α)).varpiEnd mα := by
    intro α
    have h := hz α
    rw [CerednikDrinfeld.GradedCartierModuleData.nMap_nMk, ← map_zero ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).nMk, Prod.zero_eq_mk, NInj.nMk_eq_nMk_iff] at h
    obtain ⟨t, ht1, ht2⟩ := h
    have ht1' : MvFormalGroup.CartierModule.verschiebungInt t = bc α a - 0 := ht1
    have ht2' : MvFormalGroup.CartierModule.endAct (X.map (φ α)).varpiEnd t = 0 - bc α b := ht2
    rw [sub_zero] at ht1'
    rw [zero_sub] at ht2'
    exact ⟨t, ht1'.symm, neg_eq_iff_eq_neg.mp ht2'.symm⟩
  choose mα hma hmb using hz'
  obtain ⟨a', ha', hbca'⟩ := peel a mα (fun α => hma α)
  have hb : b + (X.toGradedCartierModuleData j hc).varpi a' = 0 :=
    inj _ (fun α => by
      erw [map_add]
      rw [hbcPi, hbca', hmb]
      exact neg_add_cancel _)
  rw [ha', eq_neg_of_add_eq_zero_left hb]
  exact (X.toGradedCartierModuleData j hc).nMk_verschiebung_neg_varpi a'

end S_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero (solution)
