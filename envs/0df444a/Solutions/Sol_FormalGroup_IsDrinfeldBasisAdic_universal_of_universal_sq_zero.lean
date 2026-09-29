-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.universal_of_universal_sq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ab6ab46e-578a-5b2c-9506-f3c330846232

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_lift_of_smallExtension_of_sqZero
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_universal_of_universal_sq_zero
p2m_attr_erase "instance" "IsLocalRing.SmallExtension.algebra MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "IsLocalRing.SmallExtension.snd_pair IsLocalRing.SmallExtension.res_mk IsLocalRing.SmallExtension.snd_apply IsLocalRing.SmallExtension.coe_diag IsLocalRing.SmallExtension.fst_pair IsLocalRing.SmallExtension.fst_apply FormalGroup.ofPair_toPowerSeries IsLocalRing.SmallExtension.mk_thetaLiftAlgHom FormalGroup.LawIso.map_series IsLocalRing.SmallExtension.fst_pairRingHom FormalGroup.LawIso.ofPair_series FormalGroup.LawHom.ofPair_series IsLocalRing.SmallExtension.snd_pairRingHom IsLocalRing.SmallExtension.snd_pairAlgHom IsLocalRing.SmallExtension.fst_pairAlgHom FormalGroup.LawHom.map_series IsLocalRing.SmallExtension.fst_thetaLift IsLocalRing.SmallExtension.mk_thetaLift IsLocalRing.SmallExtension.fst_thetaLiftAlgHom MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

p2m_open "FormalGroup~isComm_map IsLocalRing"

namespace DW2R1f

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

end DW2R1f

set_option maxHeartbeats 6400000 in

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
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)) :
    (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
          ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
            (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
            ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) := by

  suffices main : ∀ (n : ℕ) (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T],
      (maximalIdeal T) ^ (n + 1) = ⊥ →
      ∀ (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
          ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
            (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
            ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 by
    intro T _ _ _ _ resT hresT hkerT hresT₀ G _ hG
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
    have hN1 : (maximalIdeal T) ^ (N + 1) = ⊥ := by
      rw [pow_succ, hN, zero_mul, Ideal.zero_eq_bot]
    exact main N T hN1 resT hresT hkerT hresT₀ G hG
  intro n
  induction n with
  | zero =>
    intro T _ _ _ _ h1 resT hresT hkerT hresT₀ G _ hG
    have hm : maximalIdeal T = ⊥ := by simpa using h1
    have hq : (q : T) = 0 := by
      have hmem : (q : T) ∈ RingHom.ker resT := by
        rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
      rw [hkerT, hm] at hmem
      exact (Submodule.mem_bot T).mp hmem
    have h2 : (maximalIdeal T) ^ 2 = ⊥ := by rw [hm, pow_two, Ideal.bot_mul]
    exact hFu1 T resT hresT hkerT hresT₀ h2 hq G hG
  | succ n ih =>
    intro T _ _ _ _ hT resT hresT hkerT hresT₀ G _ hG

    set I : Ideal T := (maximalIdeal T) ^ (n + 1) with hI
    have hIle : I ≤ maximalIdeal T := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hIne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal T).ne_top (top_le_iff.mp (h ▸ hIle))
    haveI : Nontrivial (T ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
    haveI : IsLocalRing (T ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hIker : ∀ a ∈ I, resT a = 0 := fun a ha => by
      have h' : a ∈ maximalIdeal T := hIle ha
      rw [← hkerT] at h'
      exact h'
    let resS : T ⧸ I →+* k := Ideal.Quotient.lift I resT hIker
    have hresS_mk : ∀ t : T, resS (Ideal.Quotient.mk I t) = resT t := fun t => Ideal.Quotient.lift_mk I resT hIker
    have hresS : Function.Surjective resS := fun y => by
      obtain ⟨t, rfl⟩ := hresT y
      exact ⟨Ideal.Quotient.mk I t, hresS_mk t⟩
    have hkerS : RingHom.ker resS = maximalIdeal (T ⧸ I) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resS hresS)
    have hresS₀ : ∀ w : W₀, resS (algebraMap W₀ (T ⧸ I) w) = res₀ w := fun w => by
      rw [← Ideal.Quotient.mk_algebraMap, hresS_mk, hresT₀]
    let σ : T →ₐ[W₀] T ⧸ I := Ideal.Quotient.mkₐ W₀ I
    have hσmk : ∀ t : T, σ t = Ideal.Quotient.mk I t := fun t => rfl
    have hσ : Function.Surjective σ := Ideal.Quotient.mkₐ_surjective W₀ I
    have hσres : ∀ t : T, resS (σ t) = resT t := fun t => hresS_mk t
    have hσker : RingHom.ker σ.toRingHom = I := by
      ext t
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem
    have hsmall : RingHom.ker σ.toRingHom * maximalIdeal T = ⊥ := by
      rw [hσker, hI, ← pow_succ, hT]

    have hS : (maximalIdeal (T ⧸ I)) ^ (n + 1) = ⊥ := by
      have hle : maximalIdeal (T ⧸ I) ≤ (maximalIdeal T).map (Ideal.Quotient.mk I) := by
        intro x hx
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
        have ht : t ∈ maximalIdeal T := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
          exact fun hu => hx (hu.map (Ideal.Quotient.mk I))
        exact Ideal.mem_map_of_mem _ ht
      refine le_bot_iff.mp ?_
      calc (maximalIdeal (T ⧸ I)) ^ (n + 1)
          ≤ ((maximalIdeal T).map (Ideal.Quotient.mk I)) ^ (n + 1) := Ideal.pow_right_mono hle _
        _ = ((maximalIdeal T) ^ (n + 1)).map (Ideal.Quotient.mk I) := (Ideal.map_pow _ _ _).symm
        _ = ⊥ := by rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

    let Gσ : FormalGroup (T ⧸ I) := G.map σ.toRingHom
    haveI : Gσ.IsComm := DW2R1f.isComm_map G σ.toRingHom
    have hGσ : G.IsBaseChange σ.toRingHom Gσ := rfl
    have hcomp : resS.comp σ.toRingHom = resT := RingHom.ext fun t => hσres t
    have hGσ₀ : Gσ.IsBaseChange resS F₀ := by
      show F₀.toPowerSeries = MvPowerSeries.map resS (MvPowerSeries.map σ.toRingHom G.toPowerSeries)
      rw [← RingHom.comp_apply (MvPowerSeries.map resS) (MvPowerSeries.map σ.toRingHom),
        ← MvPowerSeries.map_comp, hcomp]
      exact hG

    obtain ⟨φbar, ⟨hφbar, Gbar', hbcbar, ψbar, hψbar⟩, huniqS⟩ := ih (T ⧸ I) hS resS hresS hkerS hresS₀ Gσ hGσ₀
    obtain ⟨φ, ⟨hσφ, G', hbc, ψ, hψ⟩, huniqT⟩ :=
      FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_lift_of_smallExtension_of_sqZero
        q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu hFu1 T resT hresT hkerT hresT₀ (T ⧸ I) resS hresS hkerS
        σ hσ hσres hsmall G hG Gσ hGσ φbar hφbar Gbar' hbcbar ψbar hψbar
    refine ⟨φ, ⟨fun r => ?_, G', hbc, ψ, hψ⟩, ?_⟩
    · rw [← hσres, show σ (φ r) = φbar r from by rw [← hσφ]; rfl, hφbar]
    · rintro φ₂ ⟨hφ₂, G₂', hbc₂, ψ₂, hψ₂⟩
      have hcls : σ.comp φ₂ = φbar := by
        apply huniqS
        refine ⟨fun r => by rw [AlgHom.comp_apply, hσres, hφ₂], G₂'.map σ.toRingHom, ?_, ?_⟩
        · show (G₂'.map σ.toRingHom).toPowerSeries = MvPowerSeries.map (σ.comp φ₂).toRingHom Fu.toPowerSeries
          rw [show (σ.comp φ₂).toRingHom = σ.toRingHom.comp φ₂.toRingHom from rfl, MvPowerSeries.map_comp,
            RingHom.comp_apply]
          show MvPowerSeries.map σ.toRingHom G₂'.toPowerSeries = _
          rw [hbc₂]
        · obtain ⟨θ, hθ⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map σ.toRingHom ψ₂.toLawHom
            (G₂'.map σ.toRingHom) Gσ rfl hGσ
          refine ⟨⟨θ, ?_⟩, fun m => ?_⟩
          · rw [hθ, PowerSeries.coeff_map]
            exact ψ₂.isUnit_coeff_one.map _
          · show resS (PowerSeries.coeff m θ.series) = _
            rw [hθ, PowerSeries.coeff_map, show σ.toRingHom (PowerSeries.coeff m ψ₂.series) =
              σ (PowerSeries.coeff m ψ₂.series) from rfl, hσres, hψ₂]
      exact huniqT φ₂ ⟨hcls, G₂', hbc₂, ψ₂, hψ₂⟩

end S_FormalGroup_IsDrinfeldBasisAdic_universal_of_universal_sq_zero
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_universal_of_universal_sq_zero (solution)
