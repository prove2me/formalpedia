-- Prove2me | solution 1 for Deformation.HondaSystem.exists_splitCoordinates_lawful_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/02e6b247-cce2-5e60-8970-b62cc057cddc

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Deformation_SplitCoordinates
import Theorems.Thm_PDivisibleGroup_exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp
import Theorems.Thm_Deformation_HondaSystem_exists_mvFormalGroup_basis_coeff_eq_normalForm
import Theorems.Thm_Deformation_HondaSystem_finrank_eq_of_isCompl_of_bijective_tensorProduct_comul
import Theorems.Thm_Deformation_HondaSystem_exists_lift_linearPart_map_eq_one_of_coeff_eq
import Theorems.Thm_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp
import Theorems.Thm_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
import Theorems.Thm_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot
import Theorems.Thm_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_splitCoordinates_lawful_normalForm
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift"
p2m_attr_erase "simp" "Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

open Deformation Deformation.HondaSystem in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x) :
    ∃ 𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π, 𝒮.Lawful ∧ 𝒮.NormalForm := by
  classical

  obtain ⟨hc, he, Gc, _instCRGc, _instHGc, _instCocGc, _instFinGc, Ge, _instCRGe, _instHGe, _instCocGe, _instFinGe,
    sc, se, qc, πe, σ, Θ, hsum, hGcloc, hGered, hGeunr, hsc, hrankGc, hkersc, hse, hrankGe, hkerse, hqc, hπe, hkerπe,
    hπeσ, hkerqc, hΘ, hΘapply, hqcs, hπes, hsσ, hΘs⟩ :=
    PDivisibleGroup.exists_tower_isLocalRing_isReduced_bijective_tensorProduct_comul_zmodp p r G s hs hrankG hkerG

  obtain ⟨d, Φ, hΦcomm, κ, b, abar, hκsurj, hκker, hκs, hκε, hκrad, hκeval, hκΔ, hrkquot, hd, hkerpow, hκinj, hκsurjj,
    habar0, habartend, habarcoef, h0, h1⟩ :=
    Deformation.HondaSystem.exists_mvFormalGroup_basis_coeff_eq_normalForm
      p hp hker r H₁ G s hs hrankG hkerG hunipG π hπ hπker hπF hπV hπs
      hc Gc Ge sc qc πe Θ hGcloc hGered hsc hrankGc hkersc hqc hΘ hΘapply hqcs

  obtain ⟨a, ha_map, ha_const, -, hlin0, hlin1⟩ :=
    Deformation.HondaSystem.exists_lift_linearPart_map_eq_one_of_coeff_eq p hker abar habar0 h0 h1

  obtain ⟨Et, _instCREt, _instHEt, _instCocEt, _instFreeEt, _instFinEt, _instEtaleEt, st, θe, hθe, hθecomp, hst, hkerst,
    -, hpts⟩ :=
    PDivisibleGroup.exists_formallyEtale_tower_bijective_baseChange_zmodp p hp hker Ge hGered se hse hkerse

  have hcompat_e : ∀ (x : Fin r → 𝓞) (v : ℕ),
      DieudonneModule.map (ZMod p) p (se v) (DieudonneModule.map (ZMod p) p (πe (v + 1)) (π (v + 1) x)) =
        DieudonneModule.map (ZMod p) p (πe v) (π v x) := by
    intro x v
    rw [← DieudonneModule.map_comp, ← hπes v, DieudonneModule.map_comp, hπs]
  have star := fun i : Fin d =>
    PDivisibleGroup.exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp p hp hker Ge se Et st hst θe hθe hθecomp
      (fun v => DieudonneModule.map (ZMod p) p (πe v) (π v ((b i : H₁.L) : Fin r → 𝓞)))
      (fun v => hcompat_e _ v)
  choose ĉ hĉst hĉε hĉreal using star

  obtain ⟨Mc, Met, hcompl, hstab_c, hstab_e, hpowF, hFsurj, hMetle, hMet_iff, hMc_iff, hfreeMc, hfreeMet, hranksum,
    hLinf, hsh1le, hsh1ge, hsh2⟩ :=
    Deformation.HondaSystem.exists_isCompl_pow_F_le_and_L_inf_eq_bot p hp hker r H₁

  have hrkMc : Module.finrank 𝓞 Mc = hc :=
    Deformation.HondaSystem.finrank_eq_of_isCompl_of_bijective_tensorProduct_comul
      p hp hker r H₁ G s hs hrankG hkerG hunipG π hπ hπker hπF hπV hπs
      hc Gc Ge sc qc πe Θ hGcloc hGered hsc hrankGc hkersc hqc hΘ hΘapply hqcs Mc Met hcompl hfreeMc hMet_iff hMc_iff
  have hrkMet : Module.finrank 𝓞 Met = he := by omega

  have h4d := fun v =>
    Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct p hp hker r H₁ G s π hπ hπker hπF
      hπs v (Gc v) (Ge v) (qc v) (πe v) (Θ v) (hΘ v) (hΘapply v) (hGcloc v) (hGered v) Mc Met hMet_iff hMc_iff

  have hreal_c : ∀ (v : ℕ) (i : Fin d), ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (Gc v)),
      DieudonneModule.of (ZMod p) p (Gc v) n u =
        DieudonneModule.map (ZMod p) p (qc v) (π v ((b i : H₁.L) : Fin r → 𝓞)) ∧
      (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (Gc v)).coeff ⟨n - 1 - k, by omega⟩ = κ v (abar i k)) ∧
      (∀ k, n ≤ k → κ v (abar i k) = 0) := by
    intro v i
    obtain ⟨n, u, hu⟩ := DieudonneModule.exists_of (DieudonneModule.map (ZMod p) p (qc v) (π v ((b i : H₁.L) : Fin r → 𝓞)))
    refine ⟨n, u, hu, fun k hk => habarcoef i v n u hu k hk, fun k hk => ?_⟩
    have hle : n ≤ k + 1 := by omega
    have hu' : DieudonneModule.of (ZMod p) p (Gc v) (k + 1) (wittHomShiftLE (ZMod p) p (Gc v) hle u) =
        DieudonneModule.map (ZMod p) p (qc v) (π v ((b i : H₁.L) : Fin r → 𝓞)) := by
      rw [DieudonneModule.of_shiftLE, hu]
    have := habarcoef i v (k + 1) _ hu' k (by omega)
    rw [← this, coe_wittHomShiftLE]
    exact TruncWitt.coeff_shiftLE_of_lt hle _ _ (by simp only []; omega)

  refine ⟨{ d := d, hc := hc, he := he, Gc := Gc, Ge := Ge, sc := sc, se := se, qc := qc, πe := πe, σ := σ, Θ := Θ,
            Φ₀ := Φ, κ := κ, Et := Et, st := st, θe := θe, ĉ := ĉ, Mc := Mc, Met := Met, α := b, abar := abar, a := a },
    ?_, ?_⟩
  · exact {
      hc_add_he := hsum
      isLocalRing_Gc := hGcloc
      isReduced_Ge := hGered
      isCocomm_Gc := _instCocGc
      isCocomm_Ge := _instCocGe
      finite_Gc := _instFinGc
      finite_Ge := _instFinGe
      sc_surjective := hsc
      se_surjective := hse
      finrank_Gc := hrankGc
      finrank_Ge := hrankGe
      ker_sc := hkersc
      ker_se := hkerse
      qc_surjective := hqc
      πe_surjective := hπe
      ker_πe := hkerπe
      πe_comp_σ := hπeσ
      ker_qc := hkerqc
      Θ_bijective := hΘ
      Θ_apply := hΘapply
      qc_comp_s := hqcs
      πe_comp_s := hπes
      s_comp_σ := hsσ
      Θ_comp_s := hΘs
      formallyUnramified_Ge := hGeunr
      isComm_Φ₀ := hΦcomm
      κ_surjective := hκsurj
      ker_κ := hκker
      sc_comp_κ := hκs
      counit_κ_X := hκε
      κ_X_mem_radical := hκrad
      κ_eval := hκeval
      comul_κ_X := hκΔ
      finrank_quot_nthSeries := hrkquot
      d_eq_finrank_cotangent := hd
      ker_κ_le_pow := hkerpow
      κ_injective_joint := hκinj
      κ_surjective_joint := hκsurjj
      isCocomm_Et := _instCocEt
      free_Et := _instFreeEt
      finite_Et := _instFinEt
      formallyEtale_Et := _instEtaleEt
      st_surjective := hst
      ker_st := hkerst
      θe_bijective := hθe
      θe_comp := hθecomp
      bijective_comp_mk := fun g _ _ _ v => hpts g v
      st_ĉ := fun i k v => hĉst i k v
      counit_ĉ := fun i k v => hĉε i k v
      realisation_etale := fun v i => hĉreal i v
      isCompl := hcompl
      F_mem_Mc := fun m hm => (hstab_c m hm).1
      V_mem_Mc := fun m hm => (hstab_c m hm).2
      F_mem_Met := fun m hm => (hstab_e m hm).1
      V_mem_Met := fun m hm => (hstab_e m hm).2
      pow_F_Mc := hpowF
      F_surjOn_Met := hFsurj
      Met_le_range_F := hMetle
      mem_Met_iff := hMet_iff
      mem_Mc_iff := hMc_iff
      free_Mc := hfreeMc
      free_Met := hfreeMet
      finrank_Mc := hrkMc
      finrank_Met := hrkMet
      L_inf_Met := hLinf
      sh1_le_Lc := hsh1le
      sh1_ge_Lc := hsh1ge
      sh2_Lc := hsh2
      map_πe_π_eq_zero := fun v => (h4d v).1
      map_qc_π_eq_zero := fun v => (h4d v).2
      a_map := ha_map
      constantCoeff_a := ha_const
      abar_tendsto := habartend
      realisation_conn := hreal_c }
  · exact ⟨hlin0, hlin1⟩

end S_Deformation_HondaSystem_exists_splitCoordinates_lawful_normalForm
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_splitCoordinates_lawful_normalForm (solution)
