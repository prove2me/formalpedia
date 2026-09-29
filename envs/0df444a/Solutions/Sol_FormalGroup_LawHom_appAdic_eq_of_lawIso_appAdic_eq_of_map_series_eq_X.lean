-- Prove2me | solution 1 for FormalGroup.LawHom.appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a59a6330-5cc1-532e-af3e-d2e2f423a7ac

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
import Theorems.Thm_FormalGroup_LawHom_exists_comp_appAdic_eq
import Theorems.Thm_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawHom_appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

universe u

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] {T k : Type u} [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Field k] [CharP k q]
    (res : T →+* k) (hres : Function.Surjective res) (hker : RingHom.ker res = maximalIdeal T)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (F₁ F₂ G : FormalGroup T) [G.IsComm] (hF₁ : F₁.IsBaseChange res F₀) (hG : G.IsBaseChange res F₀)
    (ψ₁ : FormalGroup.LawIso F₁ G) (ψ₂ : FormalGroup.LawIso F₂ G)
    (hψ₁ : ∀ n : ℕ, res (PowerSeries.coeff n ψ₁.series) = if n = 1 then 1 else 0)
    (hψ₂ : ∀ n : ℕ, res (PowerSeries.coeff n ψ₂.series) = if n = 1 then 1 else 0)
    (σ : FormalGroup.LawHom F₁ F₂) (hσ : PowerSeries.map res σ.series = PowerSeries.X)
    (a₁ a₂ : T) (ha₁ : a₁ ∈ maximalIdeal T) (ha₂ : a₂ ∈ maximalIdeal T)
    (h : ψ₁.toLawHom.appAdic (maximalIdeal T) a₁ = ψ₂.toLawHom.appAdic (maximalIdeal T) a₂) :
    σ.appAdic (maximalIdeal T) a₁ = a₂ := by
  classical
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ res x = 0 := fun x => by rw [← hker, RingHom.mem_ker]
  have em : ∀ (S' : Type u) [CommRing S'] (f : T →+* S') (p : PowerSeries T), MvPowerSeries.map f p = PowerSeries.map f p :=
    fun _ _ _ _ => rfl

  have hev : ∀ (b : T), b ∈ maximalIdeal T → ∀ {F' G' : FormalGroup T} (θ : FormalGroup.LawHom F' G'),
      (θ.series = PowerSeries.X → θ.appAdic (maximalIdeal T) b = b) ∧ θ.appAdic (maximalIdeal T) b ∈ maximalIdeal T := by
    intro b hb F' G' θ
    obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal T) b hb
    have heX : e PowerSeries.X = b := by rw [← Polynomial.coe_X, hep, Polynomial.eval_X]
    have happ : θ.appAdic (maximalIdeal T) b = e θ.series := he θ.series
    refine ⟨fun hX => by rw [happ, hX, heX], ?_⟩
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr θ.constantCoeff_series
    rw [happ, hg, map_mul, heX]
    exact Ideal.mul_mem_right _ _ hb

  obtain ⟨ω, hωs, hωapp⟩ := FormalGroup.LawHom.exists_comp_appAdic_eq σ ψ₂.toLawHom
  have hσs : PowerSeries.HasSubst σ.series := PowerSeries.HasSubst.of_constantCoeff_zero' σ.constantCoeff_series
  have hψ₁res : PowerSeries.map res ψ₁.series = PowerSeries.X := by
    ext m; rw [PowerSeries.coeff_map, hψ₁ m, PowerSeries.coeff_X]
  have hψ₂res : PowerSeries.map res ψ₂.series = PowerSeries.X := by
    ext m; rw [PowerSeries.coeff_map, hψ₂ m, PowerSeries.coeff_X]
  have hωres : PowerSeries.map res ω.series = PowerSeries.map res ψ₁.toLawHom.series := by
    rw [show ψ₁.toLawHom.series = ψ₁.series from rfl, hψ₁res, hωs, show ψ₂.toLawHom.series = ψ₂.series from rfl, ← em,
      PowerSeries.map_subst hσs]
    try simp only [em]
    rw [hσ, hψ₂res, PowerSeries.X_subst]

  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal T).mp inferInstance
  have hn' : maximalIdeal T ^ n = ⊥ := by rw [hn, Ideal.zero_eq_bot]
  have hkern : RingHom.ker res ^ n = ⊥ := by rw [hker, hn']
  have hqn : (q : T) ^ n = 0 := by
    have hq : (q : T) ∈ maximalIdeal T := by rw [hmem, map_natCast, CharP.cast_eq_zero]
    have : (q : T) ^ n ∈ maximalIdeal T ^ n := Ideal.pow_mem_pow hq n
    rwa [hn', Ideal.mem_bot] at this
  have hrig := FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot q res hres n hkern hqn F₀ hF₀
    F₁ G hF₁ hG ω ψ₁.toLawHom hωres

  have h1 : ψ₂.toLawHom.appAdic (maximalIdeal T) (σ.appAdic (maximalIdeal T) a₁) =
      ψ₂.toLawHom.appAdic (maximalIdeal T) a₂ := by
    rw [← hωapp T (maximalIdeal T) a₁ ha₁, ← h]
    unfold FormalGroup.LawHom.appAdic FormalGroup.LawHom.app
    rw [hrig]

  obtain ⟨ψ₂', h21, -⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X ψ₂
  obtain ⟨κ, hκs, hκapp⟩ := FormalGroup.LawHom.exists_comp_appAdic_eq ψ₂.toLawHom ψ₂'.toLawHom
  have hκX : κ.series = PowerSeries.X := by rw [hκs]; exact h21
  have hb₁ := (hev _ ha₁ σ).2
  calc σ.appAdic (maximalIdeal T) a₁ = κ.appAdic (maximalIdeal T) (σ.appAdic (maximalIdeal T) a₁) :=
        ((hev _ hb₁ κ).1 hκX).symm
    _ = ψ₂'.toLawHom.appAdic (maximalIdeal T) (ψ₂.toLawHom.appAdic (maximalIdeal T) (σ.appAdic (maximalIdeal T) a₁)) :=
        hκapp T _ _ hb₁
    _ = ψ₂'.toLawHom.appAdic (maximalIdeal T) (ψ₂.toLawHom.appAdic (maximalIdeal T) a₂) := by rw [h1]
    _ = κ.appAdic (maximalIdeal T) a₂ := (hκapp T _ _ ha₂).symm
    _ = a₂ := (hev _ ha₂ κ).1 hκX

end S_FormalGroup_LawHom_appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X
end P2MW
export P2MW.S_FormalGroup_LawHom_appAdic_eq_of_lawIso_appAdic_eq_of_map_series_eq_X (solution)
