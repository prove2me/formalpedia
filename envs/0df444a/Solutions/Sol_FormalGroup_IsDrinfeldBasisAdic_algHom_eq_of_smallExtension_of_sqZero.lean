-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.algHom_eq_of_smallExtension_of_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/628d7c0a-7151-5db8-9529-b3c2ceb9e7d9

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_IsLocalRing_SmallExtensionTangent
import Definitions.Def_FormalGroup_FibreProductGluing
import Theorems.Thm_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_algHom_eq_of_smallExtension_of_sqZero
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing IsLocalRing.SmallExtension

namespace R1dUAux

namespace LawHom

private theorem _root_.R1dUAux.LawHom.exists_cast {R : Type} [CommRing R] {F F' G G' : FormalGroup R} (hF : F = F') (hG : G = G')
    (θ : FormalGroup.LawHom F G) : ∃ θ' : FormalGroup.LawHom F' G', θ'.series = θ.series := by
  subst hF; subst hG; exact ⟨θ, rfl⟩

end LawHom
p2m_export "R1dUAux" "LawHom.exists_cast"
namespace LawIso
private theorem _root_.R1dUAux.LawIso.exists_cast {R : Type} [CommRing R] {F F' G G' : FormalGroup R} (hF : F = F') (hG : G = G')
    (θ : FormalGroup.LawIso F G) : ∃ θ' : FormalGroup.LawIso F' G', θ'.series = θ.series := by
  subst hF; subst hG; exact ⟨θ, rfl⟩

end LawIso
p2m_export "R1dUAux" "LawIso.exists_cast"
end R1dUAux

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hFu1 : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) → (maximalIdeal T) ^ 2 = ⊥ → (q : T) = 0 →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
          ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
            (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
            ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0))

    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (S : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [Algebra W₀ S]
    (resS : S →+* k) (hresS : Function.Surjective resS) (hkerS : RingHom.ker resS = maximalIdeal S)
    (σ : T →ₐ[W₀] S) (hσ : Function.Surjective σ) (hσres : ∀ t : T, resS (σ t) = resT t)
    (hsmall : RingHom.ker σ.toRingHom * maximalIdeal T = ⊥)

    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (Gσ : FormalGroup S) (hGσ : G.IsBaseChange σ.toRingHom Gσ)
    (φbar : PowerSeries W₀ →ₐ[W₀] S)
    (hφbar : ∀ r : PowerSeries W₀, resS (φbar r) = res₀ (PowerSeries.constantCoeff r))
    (Gbar' : FormalGroup S) (hbcbar : Fu.IsBaseChange φbar.toRingHom Gbar') (ψbar : FormalGroup.LawIso Gbar' Gσ)
    (hψbar : ∀ n : ℕ, resS (PowerSeries.coeff n ψbar.series) = if n = 1 then 1 else 0)
    (φ₁ φ₂ : PowerSeries W₀ →ₐ[W₀] T)
    (hφ₁ : σ.comp φ₁ = φbar) (hφ₂ : σ.comp φ₂ = φbar)
    (G₁' : FormalGroup T) (hbc₁ : Fu.IsBaseChange φ₁.toRingHom G₁') (ψ₁ : FormalGroup.LawIso G₁' G)
    (hψ₁ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ₁.series) = if n = 1 then 1 else 0)
    (G₂' : FormalGroup T) (hbc₂ : Fu.IsBaseChange φ₂.toRingHom G₂') (ψ₂ : FormalGroup.LawIso G₂' G)
    (hψ₂ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ₂.series) = if n = 1 then 1 else 0) :
    φ₁ = φ₂ := by
  classical

  let σr : T →+* S := σ.toRingHom
  have hσr : ∀ t, σr t = σ t := fun _ => rfl
  haveI : Nontrivial S := inferInstance
  have hJ : RingHom.ker σr ≤ maximalIdeal T := ker_le_maximalIdeal σr
  haveI hPloc : IsLocalRing (fibreProd σr) := isLocalRing_fibreProd σr hJ
  haveI hEloc : IsLocalRing (Tangent σr) := isLocalRing_tangent σr hJ
  haveI hEart : IsArtinianRing (Tangent σr) := isArtinianRing_tangent σr

  have hlift : ∀ a ∈ maximalIdeal T, resT a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hkerT]; exact ha
  let ι : ResidueField T →+* k := Ideal.Quotient.lift (maximalIdeal T) resT hlift
  have hι : ∀ t : T, ι (residue T t) = resT t := fun _ => rfl
  have hιinj : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨t, rfl⟩ := residue_surjective x
    rw [hι, ← RingHom.mem_ker, hkerT] at hx
    exact (residue_eq_zero_iff _).mpr hx
  let resE : Tangent σr →+* k := ι.comp (res σr)
  have hresE_mk : ∀ x : fibreProd σr, resE (mk σr x) = resT (fst σr x) := fun x => rfl
  have hresE_surj : Function.Surjective resE := by
    intro c; obtain ⟨t, rfl⟩ := hresT c; exact ⟨mk σr (diag σr t), rfl⟩
  have hresE_ker : RingHom.ker resE = maximalIdeal (Tangent σr) := by
    rw [← ker_res_eq_maximalIdeal σr hJ]
    ext z; simp only [RingHom.mem_ker]
    constructor
    · intro h; exact hιinj (by rw [map_zero]; exact h)
    · intro h; show ι (res σr z) = 0; rw [h, map_zero]
  have hresE_alg : ∀ w : W₀, resE (algebraMap W₀ (Tangent σr) w) = res₀ w := by
    intro w
    rw [algebraMap_tangent, hresE_mk, fst_diag, hresT₀]
  have hEsq : (maximalIdeal (Tangent σr)) ^ 2 = ⊥ := maximalIdeal_tangent_sq_eq_bot σr hsmall hJ

  have hres₀q : res₀ (q : W₀) = 0 := by
    rw [← RingHom.mem_ker, hker₀, hW₀]; exact Ideal.mem_span_singleton_self _
  have hqT : (q : T) ∈ maximalIdeal T := by
    rw [← hkerT, RingHom.mem_ker, ← map_natCast (algebraMap W₀ T), hresT₀, hres₀q]
  have hqE : (q : Tangent σr) = 0 := by
    rw [natCast_tangent_eq, mk_diag_eq_zero_iff σr hsmall]; exact hqT

  have hσres' : resS.comp σr = resT := RingHom.ext (fun t => hσres t)
  have hφ₁' : σr.comp φ₁.toRingHom = φbar.toRingHom := by
    ext r; exact congrArg (fun g : PowerSeries W₀ →ₐ[W₀] S => g r) hφ₁
  have hφ₂' : σr.comp φ₂.toRingHom = φbar.toRingHom := by
    ext r; exact congrArg (fun g : PowerSeries W₀ →ₐ[W₀] S => g r) hφ₂
  have hG₁' : Fu.map φ₁.toRingHom = G₁' := (isBaseChange_iff_map_eq _ _ _).mp hbc₁
  have hG₂' : Fu.map φ₂.toRingHom = G₂' := (isBaseChange_iff_map_eq _ _ _).mp hbc₂
  have hGbar' : Fu.map φbar.toRingHom = Gbar' := (isBaseChange_iff_map_eq _ _ _).mp hbcbar
  have hGσ : G.map σr = Gσ := (isBaseChange_iff_map_eq _ _ _).mp hGσ
  have hS1 : G₁'.map σr = Gbar' := by rw [← hG₁', map_map, hφ₁', hGbar']
  have hS2 : G₂'.map σr = Gbar' := by rw [← hG₂', map_map, hφ₂', hGbar']
  obtain ⟨θ₁, hθ₁⟩ := R1dUAux.LawHom.exists_cast hS1 hGσ (ψ₁.map σr).toLawHom
  obtain ⟨θ₂, hθ₂⟩ := R1dUAux.LawHom.exists_cast hS2 hGσ (ψ₂.map σr).toLawHom
  rw [LawIso.map_series] at hθ₁ hθ₂

  have hnilS : ∃ n : ℕ, (maximalIdeal S) ^ n = ⊥ := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S)
    refine ⟨n, ?_⟩
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  obtain ⟨n, hn⟩ := hnilS
  have hkerSn : RingHom.ker resS ^ n = ⊥ := by rw [hkerS]; exact hn
  have hresS₀ : ∀ w : W₀, resS (algebraMap W₀ S w) = res₀ w := by
    intro w; rw [← σ.commutes w]; exact (hσres _).trans (hresT₀ w)
  have hqS : (q : S) ^ n = 0 := by
    have hq𝔪 : (q : S) ∈ maximalIdeal S := by
      rw [← hkerS, RingHom.mem_ker, ← map_natCast (algebraMap W₀ S), hresS₀, hres₀q]
    have := Ideal.pow_mem_pow hq𝔪 n
    rwa [hn, Ideal.mem_bot] at this
  haveI : Gσ.IsComm := by rw [← hGσ]; exact isComm_map G σr
  have hbcS1 : Gbar'.IsBaseChange resS F₀ := by
    rw [isBaseChange_iff_map_eq, ← hGbar', map_map]
    apply FormalGroup.ext
    show MvPowerSeries.map (resS.comp φbar.toRingHom) Fu.toPowerSeries = F₀.toPowerSeries
    have : resS.comp φbar.toRingHom = res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀) :=
      RingHom.ext (fun r => hφbar r)
    rw [this]; exact hFu.symm
  have hbcS2 : Gσ.IsBaseChange resS F₀ := by
    rw [isBaseChange_iff_map_eq, ← hGσ, map_map, hσres']
    exact (isBaseChange_iff_map_eq _ _ _).mp hG
  have hmapX : ∀ (s : PowerSeries T), (∀ m : ℕ, resT (PowerSeries.coeff m s) = if m = 1 then 1 else 0) →
      PowerSeries.map resT s = PowerSeries.X := by
    intro s hs; ext m; rw [PowerSeries.coeff_map, hs, PowerSeries.coeff_X]
  have hred : PowerSeries.map resS θ₁.series = PowerSeries.map resS θ₂.series := by
    have hmm : ∀ s : PowerSeries T, PowerSeries.map resS (PowerSeries.map σr s) = PowerSeries.map resT s := by
      intro s; ext m; rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, ← hσres' ]; rfl
    rw [hθ₁, hθ₂, hmm, hmm, hmapX _ hψ₁, hmapX _ hψ₂]
  have hstar : PowerSeries.map σr ψ₁.series = PowerSeries.map σr ψ₂.series := by
    rw [← hθ₁, ← hθ₂]
    exact FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot q resS hresS n hkerSn hqS
      F₀ hF₀ Gbar' Gσ hbcS1 hbcS2 θ₁ θ₂ hred

  have hpairσ : ∀ r, σr (φ₁ r) = σr (φ₂ r) := fun r => by
    show σ (φ₁ r) = σ (φ₂ r)
    rw [← AlgHom.comp_apply, hφ₁, ← AlgHom.comp_apply, hφ₂]
  let φP : PowerSeries W₀ →ₐ[W₀] fibreProd σr := pairAlgHom σr φ₁ φ₂ hpairσ
  have hfstφP : (fst σr).comp φP.toRingHom = φ₁.toRingHom := RingHom.ext (fun r => rfl)
  have hsndφP : (snd σr).comp φP.toRingHom = φ₂.toRingHom := RingHom.ext (fun r => rfl)
  have hfstdiag : (fst σr).comp (diag σr) = RingHom.id T := RingHom.ext (fun _ => rfl)
  have hsnddiag : (snd σr).comp (diag σr) = RingHom.id T := RingHom.ext (fun _ => rfl)
  have hFuP1 : (Fu.map φP.toRingHom).map (fst σr) = G₁' := by rw [map_map, hfstφP, hG₁']
  have hFuP2 : (Fu.map φP.toRingHom).map (snd σr) = G₂' := by rw [map_map, hsndφP, hG₂']
  have hGP1 : (G.map (diag σr)).map (fst σr) = G := by rw [map_map, hfstdiag, map_id]
  have hGP2 : (G.map (diag σr)).map (snd σr) = G := by rw [map_map, hsnddiag, map_id]
  have hcoef : ∀ m, σr (PowerSeries.coeff m ψ₁.series) = σr (PowerSeries.coeff m ψ₂.series) := fun m => by
    have := congrArg (PowerSeries.coeff m) hstar
    rwa [PowerSeries.coeff_map, PowerSeries.coeff_map] at this
  let s : PowerSeries (fibreProd σr) := PowerSeries.mk fun m => pair σr _ _ (hcoef m)
  have hs1 : PowerSeries.map (fst σr) s = ψ₁.series := by
    ext m; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]; rfl
  have hs2 : PowerSeries.map (snd σr) s = ψ₂.series := by
    ext m; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]; rfl
  have hs0 : PowerSeries.constantCoeff s = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    refine (ext_iff σr).mpr ⟨?_, ?_⟩
    · rw [fst_pair, map_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact ψ₁.constantCoeff_series
    · rw [snd_pair, map_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact ψ₂.constantCoeff_series
  have hu : IsUnit (PowerSeries.coeff 1 s) := by
    rw [PowerSeries.coeff_mk]
    exact (isUnit_iff_isUnit_fst σr hJ _).mpr (by rw [fst_pair]; exact ψ₁.isUnit_coeff_one)
  obtain ⟨θ₁P, hθ₁P⟩ := R1dUAux.LawHom.exists_cast hFuP1.symm hGP1.symm ψ₁.toLawHom
  obtain ⟨θ₂P, hθ₂P⟩ := R1dUAux.LawHom.exists_cast hFuP2.symm hGP2.symm ψ₂.toLawHom
  let ψP : FormalGroup.LawIso (Fu.map φP.toRingHom) (G.map (diag σr)) :=
    LawIso.ofPair (fst σr) (snd σr) (jointlyInjective_fst_snd σr) s hs0 hu θ₁P θ₂P
      (hs1.trans hθ₁P.symm) (hs2.trans hθ₂P.symm)
  have hψP : ψP.series = s := rfl

  let mkₐ : fibreProd σr →ₐ[W₀] Tangent σr := Ideal.Quotient.mkₐ W₀ (diagMax σr)
  have hmkₐ : ∀ x, mkₐ x = mk σr x := fun _ => rfl
  let diagₐ : T →ₐ[W₀] fibreProd σr := { diag σr with commutes' := fun w => rfl }
  have hdiagₐ : ∀ t, diagₐ t = diag σr t := fun _ => rfl
  let φE : PowerSeries W₀ →ₐ[W₀] Tangent σr := mkₐ.comp φP
  let φ0 : PowerSeries W₀ →ₐ[W₀] Tangent σr := (mkₐ.comp diagₐ).comp φ₁
  have hφE : ∀ r, φE r = mk σr (φP r) := fun _ => rfl
  have hφ0 : ∀ r, φ0 r = mk σr (diag σr (φ₁ r)) := fun _ => rfl
  have hφEr : φE.toRingHom = (mk σr).comp φP.toRingHom := RingHom.ext (fun _ => rfl)
  have hφ0r : φ0.toRingHom = ((mk σr).comp (diag σr)).comp φ₁.toRingHom := RingHom.ext (fun _ => rfl)
  haveI : (G.map (diag σr)).IsComm := isComm_map _ _
  haveI hGEc : ((G.map (diag σr)).map (mk σr)).IsComm := isComm_map _ _
  have hGE : ((G.map (diag σr)).map (mk σr)).IsBaseChange resE F₀ := by
    rw [isBaseChange_iff_map_eq, map_map, map_map]
    have : (resE.comp (mk σr)).comp (diag σr) = resT :=
      RingHom.ext (fun t => by show resE (mk σr (diag σr t)) = resT t; rw [hresE_mk, fst_diag])
    rw [this]; exact (isBaseChange_iff_map_eq _ _ _).mp hG
  have hres₁ : ∀ r, resT (φ₁ r) = res₀ (PowerSeries.constantCoeff r) := fun r => by
    rw [← hσres]; show resS ((σ.comp φ₁) r) = _; rw [hφ₁]; exact hφbar r
  obtain ⟨φu, -, huniq⟩ := hFu1 (Tangent σr) resE hresE_surj hresE_ker hresE_alg hEsq hqE
    ((G.map (diag σr)).map (mk σr)) hGE

  have eE : φE = φu := by
    refine huniq φE ⟨fun r => ?_, Fu.map φP.toRingHom |>.map (mk σr), ?_, ψP.map (mk σr), fun m => ?_⟩
    · rw [hφE, hresE_mk]; exact hres₁ r
    · rw [isBaseChange_iff_map_eq, hφEr, map_map]
    · rw [LawIso.map_series, PowerSeries.coeff_map, hψP, PowerSeries.coeff_mk, hresE_mk, fst_pair]; exact hψ₁ m

  have e0 : φ0 = φu := by
    refine huniq φ0 ⟨fun r => ?_, (G₁'.map (diag σr)).map (mk σr), ?_, (ψ₁.map (diag σr)).map (mk σr), fun m => ?_⟩
    · rw [hφ0, hresE_mk, fst_diag]; exact hres₁ r
    · rw [isBaseChange_iff_map_eq, hφ0r, ← map_map, ← map_map, hG₁']
    · rw [LawIso.map_series, LawIso.map_series, PowerSeries.coeff_map, PowerSeries.coeff_map, hresE_mk, fst_diag]
      exact hψ₁ m

  apply AlgHom.ext
  intro r
  have hr : φP r = diag σr (φ₁ r) := by
    apply eq_of_fst_eq_of_mk_eq σr hsmall
    · rfl
    · rw [← hφE, ← hφ0, eE, e0]
  have h2 := congrArg (snd σr) hr
  rw [snd_diag] at h2
  exact h2.symm

#print axioms solution

end S_FormalGroup_IsDrinfeldBasisAdic_algHom_eq_of_smallExtension_of_sqZero
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_algHom_eq_of_smallExtension_of_sqZero (solution)
