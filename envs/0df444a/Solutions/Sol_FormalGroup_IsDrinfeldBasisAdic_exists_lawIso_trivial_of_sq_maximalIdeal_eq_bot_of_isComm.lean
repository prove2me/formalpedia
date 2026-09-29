-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/69f62f20-8a26-565b-83f0-9af8897393cf

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
import Theorems.Thm_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
import Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
import Theorems.Thm_FormalGroup_LawHom_exists_comp_series_eq_subst
import Theorems.Thm_FormalGroup_IsBaseChange_map_frobenius
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace QuotIsoAux

theorem isAdicComplete_of_sq_eq_bot {R : Type*} [CommRing R] (I : Ideal R) (h : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
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

end QuotIsoAux

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra k T]
    (hsq : (maximalIdeal T) ^ 2 = ⊥)
    (resT : T →+* k) (hres : ∀ a : k, resT (algebraMap k T a) = a) (hker : RingHom.ker resT = maximalIdeal T)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (hD : G.IsDrinfeldBasisAdic (maximalIdeal T) q 0 0)
    (G₀ : FormalGroup T) (hG₀ : F₀.IsBaseChange (algebraMap k T) G₀) :
    ∃ ψ : FormalGroup.LawIso G₀ G, ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero

  haveI : IsAdicComplete (maximalIdeal T) T := QuotIsoAux.isAdicComplete_of_sq_eq_bot _ hsq
  haveI : Nontrivial T := inferInstance
  haveI : CharP T q := charP_of_injective_algebraMap (algebraMap k T).injective q
  have hqT : (q : T) = 0 := CharP.cast_eq_zero T q
  have hqk : (q : k) = 0 := CharP.cast_eq_zero k q

  obtain ⟨v, hv, hqG⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (maximalIdeal T) G q).mp hD
  obtain ⟨v₀, hv₀, hqF⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) F₀ q).mp hF₀

  have cf1 : ∀ {A : Type} [CommRing A] (w : PowerSeries A),
      PowerSeries.coeff 1 (w * PowerSeries.X ^ (q * q)) = 0 := by
    intro A _ w
    rw [PowerSeries.coeff_mul_X_pow', if_neg]
    have : 2 * 2 ≤ q * q := Nat.mul_le_mul hq2 hq2
    omega
  have cfq : ∀ {A : Type} [CommRing A] (w : PowerSeries A),
      PowerSeries.coeff (q * 1) (w * PowerSeries.X ^ (q * q)) = 0 := by
    intro A _ w
    rw [PowerSeries.coeff_mul_X_pow', if_neg]
    have : q * 2 ≤ q * q := Nat.mul_le_mul_left q hq2
    omega
  have cfqq : ∀ {A : Type} [CommRing A] (w : PowerSeries A),
      PowerSeries.coeff (q * (q * 1)) (w * PowerSeries.X ^ (q * q)) = PowerSeries.constantCoeff w := by
    intro A _ w
    rw [mul_one, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]

  have hcomp : resT.comp (algebraMap k T) = RingHom.id k := RingHom.ext hres
  have hG₀' : G₀.IsBaseChange resT F₀ := by
    unfold FormalGroup.IsBaseChange at hG₀ ⊢
    rw [hG₀, ← RingHom.comp_apply (MvPowerSeries.map resT) (MvPowerSeries.map (algebraMap k T)),
      ← MvPowerSeries.map_comp, hcomp, MvPowerSeries.map_id, RingHom.id_apply]

  obtain ⟨θ, hθ⟩ := FormalGroup.exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
    resT (by rw [hker]; exact hsq) q hqT F₀ G₀ G hG₀' hG
  obtain ⟨η, hη⟩ := FormalGroup.exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
    (RingHom.id k) (by rw [(RingHom.injective_iff_ker_eq_bot (RingHom.id k)).mp (fun _ _ h => h), pow_two, Ideal.bot_mul]) q hqk F₀ F₀ F₀
    (by unfold FormalGroup.IsBaseChange; rw [MvPowerSeries.map_id, RingHom.id_apply])
    (by unfold FormalGroup.IsBaseChange; rw [MvPowerSeries.map_id, RingHom.id_apply])

  obtain ⟨θ₁, hθ₁⟩ := FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero q θ
    (by rw [hθ, hqG]; exact cf1 v)
  obtain ⟨θ₂, hθ₂⟩ := FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero q θ₁
    (by rw [hθ₁, hθ, hqG]; exact cfq v)
  obtain ⟨η₁, hη₁⟩ := FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero q η
    (by rw [hη, hqF]; exact cf1 v₀)
  obtain ⟨η₂, hη₂⟩ := FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero q η₁
    (by rw [hη₁, hη, hqF]; exact cfq v₀)
  have hθ₂c : ∀ n, PowerSeries.coeff n θ₂.series = PowerSeries.coeff (q * (q * n)) (G.nthSeries q) := by
    intro n; rw [hθ₂, hθ₁, hθ]
  have hη₂c : ∀ n, PowerSeries.coeff n η₂.series = PowerSeries.coeff (q * (q * n)) (F₀.nthSeries q) := by
    intro n; rw [hη₂, hη₁, hη]
  have hθ₂u : IsUnit (PowerSeries.coeff 1 θ₂.series) := by
    rw [hθ₂c, hqG, cfqq]; exact PowerSeries.isUnit_iff_constantCoeff.mp hv
  have hη₂u : IsUnit (PowerSeries.coeff 1 η₂.series) := by
    rw [hη₂c, hqF, cfqq]; exact PowerSeries.isUnit_iff_constantCoeff.mp hv₀

  have hbc1 := FormalGroup.IsBaseChange.map_frobenius q F₀ (algebraMap k T) G₀ hG₀
  have hbc2 := FormalGroup.IsBaseChange.map_frobenius q _ (algebraMap k T) _ hbc1
  obtain ⟨α, hα⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map (algebraMap k T) η₂ _ _ hbc2 hG₀
  have hαu : IsUnit (PowerSeries.coeff 1 α.series) := by
    rw [hα, PowerSeries.coeff_map]; exact hη₂u.map _
  obtain ⟨α', hα'1, hα'2⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X (⟨α, hαu⟩ : FormalGroup.LawIso _ _)

  obtain ⟨κ, hκ, hκ1⟩ := FormalGroup.LawHom.exists_comp_series_eq_subst α'.toLawHom θ₂
  have hκu : IsUnit (PowerSeries.coeff 1 κ.series) := by
    rw [hκ1]; exact hθ₂u.mul α'.isUnit_coeff_one
  refine ⟨⟨κ, hκu⟩, fun n => ?_⟩

  have hredθ₂ : PowerSeries.map resT θ₂.series = η₂.series := by
    ext m
    rw [PowerSeries.coeff_map, hθ₂c, hη₂c, FormalGroup.IsBaseChange.nthSeries_eq_map G resT F₀ hG q,
      PowerSeries.coeff_map]
  have hredα : PowerSeries.map resT α.series = η₂.series := by
    rw [hα, ← RingHom.comp_apply (PowerSeries.map resT) (PowerSeries.map (algebraMap k T)),
      ← PowerSeries.map_comp, hcomp, PowerSeries.map_id, id]
  have hα'0 : PowerSeries.HasSubst α'.series :=
    PowerSeries.HasSubst.of_constantCoeff_zero' α'.constantCoeff_series
  have em : ∀ p : PowerSeries T, MvPowerSeries.map resT p = PowerSeries.map resT p := fun _ => rfl
  have hα'2' : PowerSeries.subst α'.series α.series = PowerSeries.X := hα'2
  have hredinv : PowerSeries.subst (PowerSeries.map resT α'.series) η₂.series = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map resT) hα'2'
    rw [PowerSeries.map_subst hα'0, hredα] at h
    rw [em, em, PowerSeries.map_X] at h
    exact h
  have hredκ : PowerSeries.map resT κ.series = PowerSeries.X := by
    rw [hκ, ← em, PowerSeries.map_subst hα'0, hredθ₂, em]
    exact hredinv
  show resT (PowerSeries.coeff n κ.series) = if n = 1 then 1 else 0
  rw [← PowerSeries.coeff_map, hredκ, PowerSeries.coeff_X]

end S_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_lawIso_trivial_of_sq_maximalIdeal_eq_bot_of_isComm (solution)
