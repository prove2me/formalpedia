-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/94eda68e-7890-5f57-971f-83b23e330427

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq
import Theorems.Thm_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false
namespace StalkOnto

theorem ker_awayLift_eq_map {S K : Type} [CommRing S] [Field K] (s : S) (x : PrimeSpectrum S) (hs : s ∉ x.asIdeal)
    (k : S →+* K) (hk : RingHom.ker k = x.asIdeal) (hu : IsUnit (k s)) :
    RingHom.ker (IsLocalization.Away.lift s hu : Localization.Away s →+* K) =
      Ideal.map (algebraMap S (Localization.Away s)) x.asIdeal := by
  have hdisj : Disjoint (↑(Submonoid.powers s) : Set S) ↑x.asIdeal :=
    Set.disjoint_left.mpr fun y hy hy' => by
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
      exact hs (x.isPrime.mem_of_pow_mem n hy')
  have hcm := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers s) (Localization.Away s) x.isPrime hdisj
  ext y
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) y
  rw [RingHom.mem_ker, IsLocalization.mk'_mem_iff]
  have hm : k (m : S) ≠ 0 := by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
    rw [← hn, map_pow]; exact pow_ne_zero _ hu.ne_zero
  have e : (IsLocalization.Away.lift s hu) (IsLocalization.mk' (Localization.Away s) r m) * k (m : S) = k r := by
    rw [← IsLocalization.Away.lift_eq (S := Localization.Away s) s hu (m : S), ← map_mul, IsLocalization.mk'_spec, IsLocalization.Away.lift_eq]
  have h1 : (IsLocalization.Away.lift s hu) (IsLocalization.mk' (Localization.Away s) r m) = 0 ↔ r ∈ x.asIdeal := by
    rw [← hk, RingHom.mem_ker]
    constructor
    · intro h0; rw [← e, h0, zero_mul]
    · intro h0; have := e; rw [h0] at this; exact (mul_eq_zero.mp this).resolve_right hm
  rw [h1]
  constructor
  · intro hr; exact Ideal.mem_map_of_mem _ hr
  · intro hr
    have : r ∈ Ideal.comap (algebraMap S (Localization.Away s)) (Ideal.map (algebraMap S (Localization.Away s)) x.asIdeal) := Ideal.mem_comap.mpr hr
    have hcm' : Ideal.comap (algebraMap S (Localization.Away s)) (Ideal.map (algebraMap S (Localization.Away s)) x.asIdeal) = x.asIdeal := hcm
    rwa [hcm'] at this

end StalkOnto

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    {K : Type} [Field K] [IsAlgClosed K] (k : S →+* K) (hk : RingHom.ker k = x.asIdeal)
    (hc' : t.IsGradedS ι ψ (k.comp g))
    (L' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').M →+ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').NMod) (hL' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS g).F.map k = (t.XS (k.comp g)).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung j,
      ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by
  classical

  obtain ⟨Sl, _instSl, jl, φl, _hφ1, _hφ2, Dl, _hDl, fl, hfl, Ll, _hLl, _hpush⟩ := hL.exists_lift
  obtain ⟨γl, _hγl, hγ⟩ := hfl.2.2.2.2.2
  obtain ⟨a, xs, hstr, _hxs, ha01⟩ := CerednikDrinfeld.GradedCartierModuleData.exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq p (Rigidified.jS ι ψ g) ((t.XS g).toGradedCartierModuleData _ hc) (fun i => fl (γl i)) hγ
  rw [hS] at ha01
  have hprod : a j * a (j + 1) = 0 := by
    fin_cases j
    · show a 0 * a (0 + 1) = 0
      rw [show ((0 : Fin 2) + 1) = 1 from rfl]; exact ha01
    · show a 1 * a (1 + 1) = 0
      rw [show ((1 : Fin 2) + 1) = 0 from rfl, mul_comm]; exact ha01
  have hann : a (j + 1) ∈ (Ideal.span {a j}).annihilator := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]; exact hprod
  by_cases hA : a j ∈ x.asIdeal
  · by_cases hB' : (Ideal.span {a j}).annihilator ≤ x.asIdeal
    ·
      have hJle₀ : (Ideal.span {a j}).radical ≤ x.asIdeal := (Ideal.IsPrime.radical_le_iff x.isPrime).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hA)
      have hJle₁ : ((Ideal.span {a j}).annihilator).radical ≤ x.asIdeal := (Ideal.IsPrime.radical_le_iff x.isPrime).mpr hB'
      obtain ⟨hinf, hnzdS⟩ := Ideal.radical_span_inf_radical_annihilator_eq_bot_of_isReduced (S := S) (a j)
      haveI instRed₀ : IsReduced (S ⧸ (Ideal.span {a j}).radical) := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
      have hkerle₀ : RingHom.ker (Ideal.Quotient.mk (Ideal.span {a j}).radical) ≤ x.asIdeal := by rw [Ideal.mk_ker]; exact hJle₀
      let x₀' : PrimeSpectrum (S ⧸ (Ideal.span {a j}).radical) := ⟨Ideal.map (Ideal.Quotient.mk (Ideal.span {a j}).radical) x.asIdeal, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerle₀⟩
      have hx₀' : x₀'.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {a j}).radical) = x.asIdeal := by
        show Ideal.comap (Ideal.Quotient.mk (Ideal.span {a j}).radical) (Ideal.map (Ideal.Quotient.mk (Ideal.span {a j}).radical) x.asIdeal) = x.asIdeal
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact sup_eq_left.mpr hJle₀
      have hJk₀ : ∀ a' ∈ (Ideal.span {a j}).radical, k a' = 0 := fun a' ha' => by rw [← RingHom.mem_ker, hk]; exact hJle₀ ha'
      let k₀' : (S ⧸ (Ideal.span {a j}).radical) →+* K := Ideal.Quotient.lift (Ideal.span {a j}).radical k hJk₀
      have hk₀' : k₀'.comp (Ideal.Quotient.mk (Ideal.span {a j}).radical) = k := RingHom.ext fun a' => Ideal.Quotient.lift_mk (Ideal.span {a j}).radical k hJk₀
      have hker₀' : RingHom.ker k₀' = x₀'.asIdeal := by
        show RingHom.ker (Ideal.Quotient.lift (Ideal.span {a j}).radical k hJk₀) = Ideal.map (Ideal.Quotient.mk (Ideal.span {a j}).radical) x.asIdeal
        rw [Ideal.ker_quotient_lift, hk]
      have hJa₀ : (Ideal.Quotient.mk (Ideal.span {a j}).radical) (a j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical (Ideal.mem_span_singleton_self _))
      obtain ⟨hch₀, hXh₀, hhV₀, hhPi₀, f₀, hf₀, hc₀, L₀, hL₀, hXr₀, hrV₀, hrPi₀, z₀, hz₀, heq₀⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul
          p ι Φ ψ hB t ht g hS hc L hL j z hz x k hk hc' L' hL' hXh hbcV hbcPi hdiv (fun i => fl (γl i)) hγ a xs hstr (Ideal.Quotient.mk (Ideal.span {a j}).radical) x₀' k₀' hk₀' hker₀' hJa₀
      haveI instRed₁ : IsReduced (S ⧸ ((Ideal.span {a j}).annihilator).radical) := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
      have hkerle₁ : RingHom.ker (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) ≤ x.asIdeal := by rw [Ideal.mk_ker]; exact hJle₁
      let x₁' : PrimeSpectrum (S ⧸ ((Ideal.span {a j}).annihilator).radical) := ⟨Ideal.map (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) x.asIdeal, Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerle₁⟩
      have hx₁' : x₁'.asIdeal.comap (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) = x.asIdeal := by
        show Ideal.comap (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) (Ideal.map (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) x.asIdeal) = x.asIdeal
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        exact sup_eq_left.mpr hJle₁
      have hJk₁ : ∀ a' ∈ ((Ideal.span {a j}).annihilator).radical, k a' = 0 := fun a' ha' => by rw [← RingHom.mem_ker, hk]; exact hJle₁ ha'
      let k₁' : (S ⧸ ((Ideal.span {a j}).annihilator).radical) →+* K := Ideal.Quotient.lift ((Ideal.span {a j}).annihilator).radical k hJk₁
      have hk₁' : k₁'.comp (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) = k := RingHom.ext fun a' => Ideal.Quotient.lift_mk ((Ideal.span {a j}).annihilator).radical k hJk₁
      have hker₁' : RingHom.ker k₁' = x₁'.asIdeal := by
        show RingHom.ker (Ideal.Quotient.lift ((Ideal.span {a j}).annihilator).radical k hJk₁) = Ideal.map (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) x.asIdeal
        rw [Ideal.ker_quotient_lift, hk]
      have hJa₁ : (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) (a (j + 1)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical hann)
      have hnzd₁ : ∀ s : S ⧸ ((Ideal.span {a j}).annihilator).radical, (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) (a j) * s = 0 → s = 0 := by
        intro s hs0
        obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hs0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hnzdS s' hs0)
      obtain ⟨hch₁, hXh₁, hhV₁, hhPi₁, f₁, hf₁, hc₁, L₁, hL₁, hXr₁, hrV₁, hrPi₁, z₁, hz₁, heq₁⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
          p ι Φ ψ hB t ht g hS hc L hL j z hz x k hk hc' L' hL' hXh hbcV hbcPi hdiv (fun i => fl (γl i)) hγ a xs hstr (Ideal.Quotient.mk ((Ideal.span {a j}).annihilator).radical) x₁' k₁' hk₁' hker₁' hJa₁ hnzd₁
      exact CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
        p ι Φ ψ t g hS hc L hL j z hz x (Ideal.span {a j}).radical ((Ideal.span {a j}).annihilator).radical hinf
        hch₀ hXh₀ hhV₀ hhPi₀ x₀' hx₀' f₀ hf₀ hc₀ L₀ hL₀ hXr₀ hrV₀ hrPi₀ z₀ hz₀ heq₀
        hch₁ hXh₁ hhV₁ hhPi₁ x₁' hx₁' f₁ hf₁ hc₁ L₁ hL₁ hXr₁ hrV₁ hrPi₁ z₁ hz₁ heq₁
    ·
      obtain ⟨s, hsAnn, hsx⟩ := Set.not_subset.mp hB'
      have hsx' : s ∉ x.asIdeal := hsx
      have hsa : s * a j = 0 := by
        have := (Submodule.mem_annihilator_span_singleton (a j) s).mp hsAnn; rwa [smul_eq_mul] at this
      have hJ : (algebraMap S (Localization.Away s)) (a j) = 0 := by
        have hu : IsUnit ((algebraMap S (Localization.Away s)) s) := IsLocalization.Away.algebraMap_isUnit s
        have := congrArg (algebraMap S (Localization.Away s)) hsa
        rw [map_mul, map_zero] at this
        exact (hu.mul_right_eq_zero).mp this
      have hdisj : Disjoint (↑(Submonoid.powers s) : Set S) ↑x.asIdeal :=
        Set.disjoint_left.mpr fun y hy hy' => by
          obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
          exact hsx' (x.isPrime.mem_of_pow_mem n hy')
      let x' : PrimeSpectrum (Localization.Away s) := ⟨Ideal.map (algebraMap S (Localization.Away s)) x.asIdeal,
        IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ x.asIdeal x.isPrime hdisj⟩
      have hx' : x'.asIdeal.comap (algebraMap S (Localization.Away s)) = x.asIdeal :=
        IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers s) (Localization.Away s) x.isPrime hdisj
      have hunit : IsUnit (k s) := isUnit_iff_ne_zero.mpr (fun h0 => hsx' (by rw [← hk]; exact h0))
      let k' : (Localization.Away s) →+* K := IsLocalization.Away.lift s hunit
      have hk' : k'.comp (algebraMap S (Localization.Away s)) = k := IsLocalization.Away.lift_comp s hunit
      have hker' : RingHom.ker k' = x'.asIdeal := StalkOnto.ker_awayLift_eq_map s x hsx' k hk hunit
      obtain ⟨hch, hXh', hhV, hhPi, f₀, hf₀, hc₀, L₀, hL₀, hXr, hrV, hrPi, z₀, hz₀, heq⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_nMap_eq_smul
          p ι Φ ψ hB t ht g hS hc L hL j z hz x k hk hc' L' hL' hXh hbcV hbcPi hdiv (fun i => fl (γl i)) hγ a xs hstr (algebraMap S (Localization.Away s)) x' k' hk' hker' hJ
      exact CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
        p ι Φ ψ hB t ht g hS hc L hL j z hz x s hsx' hch hXh' hhV hhPi x' hx' f₀ hf₀ hc₀ L₀ hL₀ hXr hrV hrPi z₀ hz₀ heq
  ·
    · have hu : IsUnit ((algebraMap S (Localization.Away (a j))) (a j)) := IsLocalization.Away.algebraMap_isUnit (a j)
      have hJ : (algebraMap S (Localization.Away (a j))) (a (j + 1)) = 0 := by
        have := congrArg (algebraMap S (Localization.Away (a j))) hprod
        rw [map_mul, map_zero] at this
        exact (hu.mul_right_eq_zero).mp this
      have hnzd : ∀ s : Localization.Away (a j), (algebraMap S (Localization.Away (a j))) (a j) * s = 0 → s = 0 :=
        fun s hs0 => (hu.mul_right_eq_zero).mp hs0
      have hdisj : Disjoint (↑(Submonoid.powers (a j)) : Set S) ↑x.asIdeal :=
        Set.disjoint_left.mpr fun y hy hy' => by
          obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
          exact hA (x.isPrime.mem_of_pow_mem n hy')
      let x' : PrimeSpectrum (Localization.Away (a j)) := ⟨Ideal.map (algebraMap S (Localization.Away (a j))) x.asIdeal,
        IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (a j)) _ x.asIdeal x.isPrime hdisj⟩
      have hx' : x'.asIdeal.comap (algebraMap S (Localization.Away (a j))) = x.asIdeal :=
        IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers (a j)) (Localization.Away (a j)) x.isPrime hdisj
      have hunit : IsUnit (k (a j)) := isUnit_iff_ne_zero.mpr (fun h0 => hA (by rw [← hk]; exact h0))
      let k' : (Localization.Away (a j)) →+* K := IsLocalization.Away.lift (a j) hunit
      have hk' : k'.comp (algebraMap S (Localization.Away (a j))) = k := IsLocalization.Away.lift_comp (a j) hunit
      have hker' : RingHom.ker k' = x'.asIdeal := StalkOnto.ker_awayLift_eq_map (a j) x hA k hk hunit
      obtain ⟨hch, hXh', hhV, hhPi, f₀, hf₀, hc₀, L₀, hL₀, hXr, hrV, hrPi, z₀, hz₀, heq⟩ :=
        CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_nMap_of_map_eq_zero_of_forall_mul_eq_zero_of_nMap_eq_smul
          p ι Φ ψ hB t ht g hS hc L hL j z hz x k hk hc' L' hL' hXh hbcV hbcPi hdiv (fun i => fl (γl i)) hγ a xs hstr (algebraMap S (Localization.Away (a j))) x' k' hk' hker' hJ hnzd
      exact CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
        p ι Φ ψ hB t ht g hS hc L hL j z hz x (a j) hA hch hXh' hhV hhPi x' hx' f₀ hf₀ hc₀ L₀ hL₀ hXr hrV hrPi z₀ hz₀ heq

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced (solution)
