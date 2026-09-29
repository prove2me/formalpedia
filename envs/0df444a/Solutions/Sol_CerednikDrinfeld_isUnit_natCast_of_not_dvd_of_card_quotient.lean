-- Prove2me | solution 1 for CerednikDrinfeld.isUnit_natCast_of_not_dvd_of_card_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/40bc372f-4f7c-56b3-9b46-4cd13dbcd752

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient

set_option autoImplicit false

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    (π : 𝒪) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (m : ℕ) (hm : ¬ r ∣ m) :
    IsUnit ((m : ℕ) : 𝒪) := by
  classical
  haveI : IsAdicComplete (Ideal.span {π}) 𝒪 := hcomplete
  have hr : r.Prime := Fact.out
  have hfin : Finite (𝒪 ⧸ Ideal.span {π}) :=
    Nat.finite_of_card_ne_zero (by rw [hres]; exact hr.ne_zero)
  letI : Fintype (𝒪 ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hcard : Fintype.card (𝒪 ⧸ Ideal.span {π}) = r := by
    rw [← Nat.card_eq_fintype_card]; exact hres
  let e : ZMod r ≃+* (𝒪 ⧸ Ideal.span {π}) := ZMod.ringEquivOfPrime (𝒪 ⧸ Ideal.span {π}) hr hcard

  have hmq : IsUnit ((m : ℕ) : 𝒪 ⧸ Ideal.span {π}) := by
    have h1 : ((m : ℕ) : 𝒪 ⧸ Ideal.span {π}) = e (m : ZMod r) := by simp [map_natCast]
    rw [h1]
    refine IsUnit.map e ?_
    have hne : (m : ZMod r) ≠ 0 := by
      intro h
      exact hm ((ZMod.natCast_eq_zero_iff m r).mp h)
    exact isUnit_iff_ne_zero.mpr hne

  obtain ⟨a, ha⟩ : ∃ a : 𝒪, (m : 𝒪) * a - 1 ∈ Ideal.span {π} := by
    obtain ⟨u, hu⟩ := hmq
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {π}) (↑u⁻¹ : 𝒪 ⧸ Ideal.span {π})
    refine ⟨a, ?_⟩
    rw [← Ideal.Quotient.eq, map_mul, map_one, map_natCast, ha, ← hu, Units.mul_inv]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  have hjac : π ∈ (⊥ : Ideal 𝒪).jacobson :=
    (IsAdicComplete.le_jacobson_bot (Ideal.span {π})) (Ideal.subset_span (Set.mem_singleton π))
  have hu1 : IsUnit (π * c + 1) := (Ideal.mem_jacobson_bot.mp hjac) c
  have hprod : (m : 𝒪) * a = π * c + 1 := by
    have : (m : 𝒪) * a - 1 = c * π := hc.symm
    linear_combination this
  have : IsUnit ((m : 𝒪) * a) := by rw [hprod]; exact hu1
  exact isUnit_of_mul_isUnit_left this

end S_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_isUnit_natCast_of_not_dvd_of_card_quotient (solution)
