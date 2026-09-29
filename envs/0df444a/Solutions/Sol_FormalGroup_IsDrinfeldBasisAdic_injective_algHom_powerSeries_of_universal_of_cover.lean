-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.injective_algHom_powerSeries_of_universal_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8f8ffc8a-0681-5950-83c3-5877417ae17b

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange
import Theorems.Thm_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem
import Theorems.Thm_FormalGroup_LawHom_exists_comp_series_eq_subst
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Theorems.Thm_IsAdicComplete_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal_of_cover

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DW2R4e

theorem isComm_map {R S : Type*} [CommRing R] [CommRing S] (F : FormalGroup R) [hF : F.IsComm] (f : R →+* S) :
    (F.map f).IsComm := by
  constructor
  show (F.map f).toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (F.map f).toPowerSeries
  have h : F.toPowerSeries = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] F.toPowerSeries := hF.comm
  have hswap : (fun i => MvPowerSeries.map f
      ((![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) R) i)) =
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] : Fin 2 → MvPowerSeries (Fin 2) S) := by
    funext i; fin_cases i <;> simp [MvPowerSeries.map_X]
  rw [FormalGroup.map_toPowerSeries]
  conv_lhs => rw [h]
  rw [MvPowerSeries.map_subst MvPowerSeries.HasSubst.X_X, hswap]

theorem map_eq_X_of {T k : Type*} [CommRing T] [CommRing k] (res : T →+* k) (s : PowerSeries T)
    (h : ∀ n : ℕ, res (PowerSeries.coeff n s) = if n = 1 then 1 else 0) :
    PowerSeries.map res s = PowerSeries.X := by
  ext n; rw [PowerSeries.coeff_map, h, PowerSeries.coeff_X]

end DW2R4e

set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra W₀ R] [IsAdicComplete (maximalIdeal R) R] [IsNoetherianRing R]
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (F : FormalGroup R) [F.IsComm] (hF : F.IsBaseChange resR F₀)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (huniv : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ x₀) = y₀ ∧ ψ.toLawHom.appAdic (maximalIdeal T) (φ x₁) = y₁)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hLT : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
          (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
          (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
          ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
            ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
              (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
              ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
                ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0))
    (φ : PowerSeries W₀ →ₐ[W₀] R)
    (hφres : ∀ r : PowerSeries W₀, resR (φ r) = res₀ (PowerSeries.constantCoeff r))
    (F' : FormalGroup R) (hbc : Fu.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' F)
    (hψ : ∀ n : ℕ, resR (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)
    (C : Type) [CommRing C] [Algebra (PowerSeries W₀) C] [IsLocalRing C]
    [Module.Finite (PowerSeries W₀) C] [IsAdicComplete (maximalIdeal C) C]
    (resC : C →+* k) (hresC : Function.Surjective resC) (hkerC : RingHom.ker resC = maximalIdeal C)
    (hresC₀ : ∀ f : PowerSeries W₀, resC (algebraMap (PowerSeries W₀) C f) = res₀ (PowerSeries.constantCoeff f))
    (Gc : FormalGroup C) (hGc : Fu.IsBaseChange (algebraMap (PowerSeries W₀) C) Gc)
    (c₀ c₁ : C) (hc₀ : c₀ ∈ maximalIdeal C) (hc₁ : c₁ ∈ maximalIdeal C)
    (hcD : Gc.IsDrinfeldBasisAdic (maximalIdeal C) q c₀ c₁)
    (hinj : Function.Injective (algebraMap (PowerSeries W₀) C)) :
    Function.Injective φ := by
  classical

  have hq0 : res₀ (q : W₀) = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  have hρs : Function.Surjective (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) :=
    hres₀.comp PowerSeries.constantCoeff_surj
  have hkerρ : RingHom.ker (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) =
      maximalIdeal (PowerSeries W₀) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hρs)
  have hloc : ∀ s ∈ maximalIdeal (PowerSeries W₀), algebraMap (PowerSeries W₀) C s ∈ maximalIdeal C := by
    intro s hs
    rw [← hkerρ, RingHom.mem_ker] at hs
    rw [← hkerC, RingHom.mem_ker, hresC₀]
    exact hs
  have hCloc : ∀ c ∈ maximalIdeal C, resC c = 0 := fun c hc => by rwa [← hkerC] at hc
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite (PowerSeries W₀) C

  have hrad : maximalIdeal C ≤ ((maximalIdeal (PowerSeries W₀)).map (algebraMap (PowerSeries W₀) C)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hP, hPprime⟩
    have hcomap : (P.comap (algebraMap (PowerSeries W₀) C)).IsMaximal := by
      have hle : maximalIdeal (PowerSeries W₀) ≤ P.comap (algebraMap (PowerSeries W₀) C) :=
        fun s hs => hP (Ideal.mem_map_of_mem _ hs)
      have hne : P.comap (algebraMap (PowerSeries W₀) C) ≠ ⊤ := Ideal.comap_ne_top _ hPprime.ne_top
      rw [← (maximalIdeal.isMaximal (PowerSeries W₀)).eq_of_le hne hle]
      exact maximalIdeal.isMaximal _
    haveI := hPprime
    have hPmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := PowerSeries W₀) P hcomap
    exact (IsLocalRing.eq_maximalIdeal hPmax).ge
  obtain ⟨a, ha⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

  rw [injective_iff_map_eq_zero]
  intro f hf
  apply hinj
  rw [map_zero]
  refine (Submodule.mem_bot C).mp ?_
  rw [← Ideal.iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite (PowerSeries W₀) C, Submodule.mem_iInf]
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; exact Submodule.mem_top
  set J : Ideal C := (maximalIdeal (PowerSeries W₀) ^ n).map (algebraMap (PowerSeries W₀) C) with hJ
  have hJle : J ≤ maximalIdeal C := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    exact fun s hs => hloc s (Ideal.pow_le_self hn.ne' hs)
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal C).ne_top (top_le_iff.mp (h ▸ hJle))
  haveI : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  haveI : IsLocalRing (C ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

  have hpow : maximalIdeal C ^ (a * n) ≤ J := by
    rw [pow_mul, hJ, Ideal.map_pow]
    exact Ideal.pow_right_mono ha n
  have hmT : maximalIdeal (C ⧸ J) ≤ (maximalIdeal C).map (Ideal.Quotient.mk J) := by
    intro x hx
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ht : t ∈ maximalIdeal C := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun hu => hx (hu.map (Ideal.Quotient.mk J))
    exact Ideal.mem_map_of_mem _ ht
  have hTnil : IsNilpotent (maximalIdeal (C ⧸ J)) := by
    refine ⟨a * n, ?_⟩
    rw [Ideal.zero_eq_bot, ← le_bot_iff]
    calc maximalIdeal (C ⧸ J) ^ (a * n) ≤ ((maximalIdeal C).map (Ideal.Quotient.mk J)) ^ (a * n) :=
          Ideal.pow_right_mono hmT _
      _ = (maximalIdeal C ^ (a * n)).map (Ideal.Quotient.mk J) := (Ideal.map_pow _ _ _).symm
      _ ≤ J.map (Ideal.Quotient.mk J) := Ideal.map_mono hpow
      _ = ⊥ := by rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  haveI : IsArtinianRing (C ⧸ J) := (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr hTnil
  haveI : IsAdicComplete (maximalIdeal (C ⧸ J)) (C ⧸ J) := IsAdicComplete.of_isNilpotent hTnil

  let π : C →+* C ⧸ J := Ideal.Quotient.mk J
  letI algT : Algebra W₀ (C ⧸ J) :=
    (π.comp ((algebraMap (PowerSeries W₀) C).comp (algebraMap W₀ (PowerSeries W₀)))).toAlgebra
  have halgT : ∀ w : W₀, algebraMap W₀ (C ⧸ J) w = π (algebraMap (PowerSeries W₀) C (algebraMap W₀ (PowerSeries W₀) w)) :=
    fun w => rfl
  have hJker : ∀ c ∈ J, resC c = 0 := fun c hc => hCloc c (hJle hc)
  let resT : C ⧸ J →+* k := Ideal.Quotient.lift J resC hJker
  have hresT_mk : ∀ c, resT (π c) = resC c := fun c => Ideal.Quotient.lift_mk J resC hJker
  have hresT : Function.Surjective resT := fun y => by
    obtain ⟨c, rfl⟩ := hresC y; exact ⟨π c, hresT_mk c⟩
  have hkerT : RingHom.ker resT = maximalIdeal (C ⧸ J) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resT hresT)
  have hresT₀ : ∀ w : W₀, resT (algebraMap W₀ (C ⧸ J) w) = res₀ w := by
    intro w
    have hcw : PowerSeries.constantCoeff (algebraMap W₀ (PowerSeries W₀) w) = w := by simp
    rw [halgT, hresT_mk, hresC₀, hcw]
  have hπloc : ∀ c ∈ maximalIdeal C, π c ∈ maximalIdeal (C ⧸ J) := by
    intro c hc; rw [← hkerT, RingHom.mem_ker, hresT_mk]; exact hCloc c hc

  let G : FormalGroup (C ⧸ J) := Gc.map π
  haveI : Gc.IsComm := by
    have : Gc = Fu.map (algebraMap (PowerSeries W₀) C) := FormalGroup.ext hGc
    rw [this]; exact DW2R4e.isComm_map Fu _
  haveI : G.IsComm := DW2R4e.isComm_map Gc π
  have hGbc : Gc.IsBaseChange π G := rfl
  have hcomp : resT.comp (π.comp (algebraMap (PowerSeries W₀) C)) =
      res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) :=
    RingHom.ext fun s => by simp only [RingHom.comp_apply, hresT_mk, hresC₀]
  have hGS : Fu.IsBaseChange (π.comp (algebraMap (PowerSeries W₀) C)) G := by
    show G.toPowerSeries = MvPowerSeries.map (π.comp (algebraMap (PowerSeries W₀) C)) Fu.toPowerSeries
    rw [MvPowerSeries.map_comp, RingHom.comp_apply]
    unfold FormalGroup.IsBaseChange at hGc
    rw [← hGc]
    rfl
  have hG : G.IsBaseChange resT F₀ := by
    show F₀.toPowerSeries = MvPowerSeries.map resT G.toPowerSeries
    unfold FormalGroup.IsBaseChange at hGS hFu
    rw [hGS, ← RingHom.comp_apply (MvPowerSeries.map resT), ← MvPowerSeries.map_comp, hcomp]
    exact hFu
  have hGD := FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange (maximalIdeal C) (maximalIdeal (C ⧸ J)) π
    hπloc Gc G hGbc q c₀ c₁ hc₀ hc₁ hcD

  obtain ⟨ρ, ⟨hρres, F'', hF'', ψT, hψT, -, -⟩, -⟩ :=
    huniv (C ⧸ J) resT hresT hkerT hresT₀ G hG (π c₀) (π c₁) (hπloc c₀ hc₀) (hπloc c₁ hc₁) hGD
  obtain ⟨χ, -, huniq⟩ := hLT (C ⧸ J) resT hresT hkerT hresT₀ G hG

  let χ₂ : PowerSeries W₀ →ₐ[W₀] C ⧸ J :=
    { toRingHom := π.comp (algebraMap (PowerSeries W₀) C), commutes' := fun w => rfl }
  have P2 : (∀ r : PowerSeries W₀, resT (χ₂ r) = res₀ (PowerSeries.constantCoeff r)) ∧
      ∃ (G' : FormalGroup (C ⧸ J)) (_ : Fu.IsBaseChange χ₂.toRingHom G') (ψ : FormalGroup.LawIso G' G),
        ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by
    obtain ⟨ψ0, hψ0, -⟩ := FormalGroup.exists_lawIso_refl_appAdic_eq_of_mem (maximalIdeal (C ⧸ J)) G
    refine ⟨fun r => ?_, G, hGS, ψ0, fun n => ?_⟩
    · exact (RingHom.congr_fun hcomp r)
    · rw [hψ0, PowerSeries.coeff_X]; split_ifs <;> simp

  have P1 : (∀ r : PowerSeries W₀, resT ((ρ.comp φ) r) = res₀ (PowerSeries.constantCoeff r)) ∧
      ∃ (G' : FormalGroup (C ⧸ J)) (_ : Fu.IsBaseChange (ρ.comp φ).toRingHom G') (ψ' : FormalGroup.LawIso G' G),
        ∀ n : ℕ, resT (PowerSeries.coeff n ψ'.series) = if n = 1 then 1 else 0 := by
    refine ⟨fun r => by rw [AlgHom.comp_apply, hρres, hφres], F'.map ρ.toRingHom, ?_, ?_⟩
    · show (F'.map ρ.toRingHom).toPowerSeries = MvPowerSeries.map (ρ.comp φ).toRingHom Fu.toPowerSeries
      rw [show (ρ.comp φ).toRingHom = ρ.toRingHom.comp φ.toRingHom from rfl, MvPowerSeries.map_comp,
        RingHom.comp_apply]
      unfold FormalGroup.IsBaseChange at hbc
      rw [← hbc]
      rfl
    · obtain ⟨θ, hθ⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map ρ.toRingHom ψ.toLawHom
        (F'.map ρ.toRingHom) F'' rfl hF''
      obtain ⟨κ, hκ, hκ1⟩ := FormalGroup.LawHom.exists_comp_series_eq_subst θ ψT.toLawHom
      have hθX : PowerSeries.map resT θ.series = PowerSeries.X := by
        apply DW2R4e.map_eq_X_of
        intro n
        rw [hθ, PowerSeries.coeff_map, show ρ.toRingHom (PowerSeries.coeff n ψ.series) = ρ (PowerSeries.coeff n ψ.series)
          from rfl, hρres, hψ]
      have hψTX : PowerSeries.map resT ψT.series = PowerSeries.X := DW2R4e.map_eq_X_of resT _ hψT
      have hθX' : MvPowerSeries.map resT θ.series = PowerSeries.X := hθX
      have hψTX' : MvPowerSeries.map resT ψT.series = PowerSeries.X := hψTX
      have hκres : ∀ n : ℕ, resT (PowerSeries.coeff n κ.series) = if n = 1 then 1 else 0 := by
        intro n
        rw [← PowerSeries.coeff_map, hκ]
        show PowerSeries.coeff n (MvPowerSeries.map resT (PowerSeries.subst θ.series ψT.series)) = _
        rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' θ.constantCoeff_series), hθX', hψTX,
          PowerSeries.subst_X (PowerSeries.HasSubst.X' : PowerSeries.HasSubst (PowerSeries.X : PowerSeries k)),
          PowerSeries.coeff_X]
      have hunit : IsUnit (PowerSeries.coeff 1 κ.series) := by
        by_contra hu
        have hm : PowerSeries.coeff 1 κ.series ∈ maximalIdeal (C ⧸ J) :=
          (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
        rw [← hkerT, RingHom.mem_ker, hκres] at hm
        simp at hm
      exact ⟨⟨κ, hunit⟩, hκres⟩

  have e : χ₂ f = (ρ.comp φ) f := by rw [huniq χ₂ P2, huniq (ρ.comp φ) P1]
  rw [AlgHom.comp_apply, hf, map_zero] at e
  exact Ideal.Quotient.eq_zero_iff_mem.mp e

end S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal_of_cover
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal_of_cover (solution)
