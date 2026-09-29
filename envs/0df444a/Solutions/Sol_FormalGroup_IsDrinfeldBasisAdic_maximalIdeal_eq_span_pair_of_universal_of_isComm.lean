-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.maximalIdeal_eq_span_pair_of_universal_of_isComm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/99eb7640-51a6-53e3-812c-12853299d07f

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_natCast_mem_pow
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange
import Theorems.Thm_FormalGroup_exists_isBaseChange
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
import Theorems.Thm_FormalGroup_IsBaseChange_isComm
import Theorems.Thm_FormalGroup_LawHom_appAdic_zero
import Theorems.Thm_FormalGroup_exists_lawIso_refl_appAdic_eq_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_maximalIdeal_eq_span_pair_of_universal_of_isComm
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast"

set_option autoImplicit false

open FormalGroup IsLocalRing

private theorem adic_of_sq_eq_bot {R : Type*} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) : IsAdicComplete I R := by
  have hpow : ∀ n, 2 ≤ n → (I ^ n • ⊤ : Submodule R R) = ⊥ := by
    intro n hn
    have : I ^ n = ⊥ := le_bot_iff.mp (h ▸ Ideal.pow_le_pow_right hn)
    rw [this]; simp
  haveI : IsHausdorff I R := ⟨fun x hx => by
    have := hx 2
    rw [hpow 2 le_rfl, SModEq.bot] at this
    exact this⟩
  haveI : IsPrecomplete I R := ⟨fun f hf => by
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt n 2 with hn | hn
    · exact (hf hn)
    · have h2 := hf hn.le
      rw [hpow 2 le_rfl, SModEq.bot] at h2
      rw [h2]⟩
  exact ⟨⟩

private theorem artinian_quot {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R)
    (hJ : (maximalIdeal R) ^ 2 ≤ J) (hJ' : J ≠ ⊤) : IsArtinianRing (R ⧸ J) := by
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ'
  haveI : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal (R ⧸ J) = (maximalIdeal R).map (Ideal.Quotient.mk J) := by
    haveI : ((maximalIdeal R).map (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact IsLocalRing.le_maximalIdeal hJ')
    exact (IsLocalRing.eq_maximalIdeal this).symm
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨2, ?_⟩
  rw [hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact hJ

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
              ψ.toLawHom.appAdic (maximalIdeal T) (φ x₀) = y₀ ∧ ψ.toLawHom.appAdic (maximalIdeal T) (φ x₁) = y₁) :
    maximalIdeal R = Ideal.span {x₀, x₁} := by
  classical
  set J : Ideal R := Ideal.span {x₀, x₁} with hJdef
  have hJle : J ≤ maximalIdeal R := by
    rw [Ideal.span_le]; rintro z hz
    rcases hz with rfl | rfl
    · exact hx₀
    · simpa using hx₁

  suffices hsuff : maximalIdeal R ≤ J ⊔ (maximalIdeal R) ^ 2 by
    refine le_antisymm ?_ hJle
    have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    simpa [pow_two, Ideal.smul_eq_mul] using hsuff

  set J' : Ideal R := J ⊔ (maximalIdeal R) ^ 2 with hJ'def
  have hJ'le : J' ≤ maximalIdeal R := sup_le hJle (Ideal.pow_le_self two_ne_zero)
  have hJ'ne : J' ≠ ⊤ := fun h => IsLocalRing.maximalIdeal.isMaximal R |>.ne_top (top_le_iff.mp (h ▸ hJ'le))

  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hqmem : (q : R) ∈ J' := by
    have h1 := FormalGroup.IsDrinfeldBasisAdic.natCast_mem_pow (maximalIdeal R) F q x₀ x₁ hx₀ hx₁ hD
    have hle : (maximalIdeal R) ^ (q * q - 1) ≤ (maximalIdeal R) ^ 2 := by
      apply Ideal.pow_le_pow_right
      have : 2 * 2 ≤ q * q := Nat.mul_le_mul hq2 hq2
      omega
    exact le_sup_right (a := J) (hle h1)
  let T : Type := R ⧸ J'
  let π : R →+* T := Ideal.Quotient.mk J'
  haveI : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hJ'ne
  haveI : IsLocalRing T := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have hπx₀ : π x₀ = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr (le_sup_left (b := (maximalIdeal R)^2) (Ideal.subset_span (by simp)))
  have hπx₁ : π x₁ = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr (le_sup_left (b := (maximalIdeal R)^2) (Ideal.subset_span (by simp)))

  have hJ'ker : J' ≤ RingHom.ker resR := hkerR.symm ▸ hJ'le
  let resT : T →+* k := Ideal.Quotient.lift J' resR (fun r hr => hJ'ker hr)
  have hresT_mk : ∀ r : R, resT (π r) = resR r := fun r => Ideal.Quotient.lift_mk J' resR _
  have hresT_surj : Function.Surjective resT := by
    intro a; obtain ⟨r, rfl⟩ := hresR a; exact ⟨π r, hresT_mk r⟩
  have hmaxT : maximalIdeal T = (maximalIdeal R).map π := by
    haveI : ((maximalIdeal R).map π).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJ'le)
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hkerT : RingHom.ker resT = maximalIdeal T :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resT hresT_surj)
  have hsqT : (maximalIdeal T) ^ 2 = ⊥ := by
    rw [hmaxT, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right

  have hker₀le : ∀ w ∈ RingHom.ker res₀, (π.comp (algebraMap W₀ R)) w = 0 := by
    intro w hw
    rw [hker₀, hW₀] at hw
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    simp only [RingHom.comp_apply, map_mul, map_natCast]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J'.mul_mem_left _ hqmem)
  let e₀ : (W₀ ⧸ RingHom.ker res₀) ≃+* k := RingHom.quotientKerEquivOfSurjective hres₀
  let s : k →+* T := (Ideal.Quotient.lift (RingHom.ker res₀) (π.comp (algebraMap W₀ R)) hker₀le).comp e₀.symm.toRingHom
  have hs : ∀ w : W₀, s (res₀ w) = π (algebraMap W₀ R w) := by
    intro w
    have he : e₀.symm (res₀ w) = Ideal.Quotient.mk _ w := by
      apply e₀.symm_apply_eq.mpr
      simp [e₀, RingHom.quotientKerEquivOfSurjective, RingHom.kerLift_mk]
    simp only [s, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he, Ideal.Quotient.lift_mk,
      RingHom.comp_apply]
  have hresT_s : ∀ a : k, resT (s a) = a := by
    intro a; obtain ⟨w, rfl⟩ := hres₀ a; rw [hs, hresT_mk, hresR₀]
  letI : Algebra k T := s.toAlgebra
  have halgk : ∀ a : k, algebraMap k T a = s a := fun a => rfl
  have hres_k : ∀ a : k, resT (algebraMap k T a) = a := fun a => (halgk a).symm ▸ hresT_s a
  haveI : IsAdicComplete (maximalIdeal T) T := adic_of_sq_eq_bot _ hsqT
  haveI : IsArtinianRing T :=
    artinian_quot J' le_sup_right hJ'ne
  have halgT : ∀ w : W₀, algebraMap W₀ T w = π (algebraMap W₀ R w) := fun w => rfl
  have hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w := by
    intro w; rw [halgT, hresT_mk, hresR₀]

  have mapmap : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
      (φ : MvPowerSeries (Fin 2) A), MvPowerSeries.map g (MvPowerSeries.map f φ) = MvPowerSeries.map (g.comp f) φ := by
    intro A B C _ _ _ f g φ; rw [MvPowerSeries.map_comp]; rfl
  have hπres : resT.comp π = resR := RingHom.ext hresT_mk
  obtain ⟨G, hG⟩ := FormalGroup.exists_isBaseChange F π
  haveI : G.IsComm := FormalGroup.IsBaseChange.isComm F π G hG
  have hGF₀ : G.IsBaseChange resT F₀ := by
    unfold FormalGroup.IsBaseChange at hG hF ⊢
    rw [hG, mapmap, hπres]; exact hF
  have hπm : ∀ r ∈ maximalIdeal R, π r ∈ maximalIdeal T := by
    intro r hr; rw [hmaxT]; exact Ideal.mem_map_of_mem _ hr
  have hDT : G.IsDrinfeldBasisAdic (maximalIdeal T) q 0 0 := by
    have h := FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange (maximalIdeal R) (maximalIdeal T) π hπm F G hG q
      x₀ x₁ hx₀ hx₁ hD
    rwa [hπx₀, hπx₁] at h
  obtain ⟨G₀, hG₀⟩ := FormalGroup.exists_isBaseChange F₀ (algebraMap k T)
  obtain ⟨ψ, hψ⟩ := FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm q k F₀ hF₀ T
    hsqT resT hres_k hkerT G hGF₀ hDT G₀ hG₀

  obtain ⟨φ, -, huniq⟩ := huniv T resT hresT_surj hkerT hresT₀ G hGF₀ 0 0 (zero_mem _) (zero_mem _) hDT

  let φ₁ : R →ₐ[W₀] T := Ideal.Quotient.mkₐ W₀ J'
  have hφ₁ : ∀ r, φ₁ r = π r := fun r => rfl
  obtain ⟨ψr, hψr_ser, hψr_app⟩ := FormalGroup.exists_lawIso_refl_appAdic_eq_of_mem (maximalIdeal T) G
  have P₁ : (∀ r : R, resT (φ₁ r) = resR r) ∧
      ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₁.toRingHom F') (ψ' : FormalGroup.LawIso F' G),
        (∀ n : ℕ, resT (PowerSeries.coeff n ψ'.series) = if n = 1 then 1 else 0) ∧
        ψ'.toLawHom.appAdic (maximalIdeal T) (φ₁ x₀) = 0 ∧ ψ'.toLawHom.appAdic (maximalIdeal T) (φ₁ x₁) = 0 := by
    refine ⟨fun r => hresT_mk r, G, ?_, ψr, ?_, ?_, ?_⟩
    · exact hG
    · intro n; rw [hψr_ser, PowerSeries.coeff_X]; split_ifs <;> simp
    · rw [hφ₁, hπx₀, hψr_app 0 (zero_mem _)]
    · rw [hφ₁, hπx₁, hψr_app 0 (zero_mem _)]

  let φ₂ : R →ₐ[W₀] T :=
    { toRingHom := s.comp resR
      commutes' := fun w => by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
          RingHom.comp_apply, hresR₀, hs, halgT] }
  have hφ₂ : ∀ r, φ₂ r = s (resR r) := fun r => rfl
  have hx₀k : resR x₀ = 0 := by rw [← RingHom.mem_ker, hkerR]; exact hx₀
  have hx₁k : resR x₁ = 0 := by rw [← RingHom.mem_ker, hkerR]; exact hx₁
  have P₂ : (∀ r : R, resT (φ₂ r) = resR r) ∧
      ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₂.toRingHom F') (ψ' : FormalGroup.LawIso F' G),
        (∀ n : ℕ, resT (PowerSeries.coeff n ψ'.series) = if n = 1 then 1 else 0) ∧
        ψ'.toLawHom.appAdic (maximalIdeal T) (φ₂ x₀) = 0 ∧ ψ'.toLawHom.appAdic (maximalIdeal T) (φ₂ x₁) = 0 := by
    refine ⟨fun r => by rw [hφ₂, hresT_s], G₀, ?_, ψ, hψ, ?_, ?_⟩
    · unfold FormalGroup.IsBaseChange at hG₀ hF ⊢
      rw [hG₀, hF, mapmap]; rfl
    · rw [hφ₂, hx₀k, map_zero, FormalGroup.LawHom.appAdic_zero (maximalIdeal T)]
    · rw [hφ₂, hx₁k, map_zero, FormalGroup.LawHom.appAdic_zero (maximalIdeal T)]
  have h12 : φ₁ = φ₂ := (huniq φ₁ P₁).trans (huniq φ₂ P₂).symm

  intro r hr
  have : π r = 0 := by
    rw [← hφ₁, h12, hφ₂, (RingHom.mem_ker).mp (hkerR.symm ▸ hr : r ∈ RingHom.ker resR), map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end S_FormalGroup_IsDrinfeldBasisAdic_maximalIdeal_eq_span_pair_of_universal_of_isComm
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_maximalIdeal_eq_span_pair_of_universal_of_isComm (solution)
