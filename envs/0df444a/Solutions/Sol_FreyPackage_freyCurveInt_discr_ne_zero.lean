-- Prove2me | solution 1 for FreyPackage.freyCurveInt_discr_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ad9e33e1-1ccb-5846-991d-3061619f8b19

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_freyCurveInt_discr_ne_zero

set_option autoImplicit false

namespace FreyArith

open FreyPackage

open WeierstrassCurve

theorem freyCurveInt_map (P : FreyPackage) :
    (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  · change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    · rw [sub_sub]
      apply Int.dvd_sub
      · calc
          (4 : ℤ) = 2 ^ 2     := by norm_num
          _       ∣ P.b ^ 2   := pow_dvd_pow_of_dvd two_dvd_b 2
          _       ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, if_neg]
        · norm_num
        · rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  · change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    · calc
        (16 : ℤ) = 2 ^ 4     := by norm_num
        _        ∣ P.b ^ 4   := pow_dvd_pow_of_dvd two_dvd_b 4
        _        ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _        ∣ _         := Int.dvd_mul_left _ _
  · rfl

theorem freyCurve_Δ (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

theorem freyCurve_c₄_eq_intCast (P : FreyPackage) : P.freyCurve.c₄ = (c₄Int P : ℚ) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve, c₄Int]
  push_cast
  field_simp
  ring

theorem c₄Int_eq_sub (P : FreyPackage) : c₄Int P = (P.c ^ P.p) ^ 2 - (P.a * P.b) ^ P.p := by
  rw [c₄Int, ← P.hFLT, mul_pow]
  ring

theorem not_dvd_c₄Int (P : FreyPackage) {q : ℤ} (hq : Prime q)
    (hqbad : q ∣ P.a * P.b * P.c) : ¬q ∣ c₄Int P := by
  intro hdvd
  rcases hq.dvd_mul.mp hqbad with hab | hc
  · rcases hq.dvd_mul.mp hab with ha | hb
    ·
      have hqb : ¬q ∣ P.b := fun hb =>
        hq.not_unit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqap : q ∣ P.a ^ P.p := dvd_pow ha P.hp0
      rw [c₄Int, dvd_add_right (dvd_add (dvd_pow hqap two_ne_zero)
        (dvd_mul_of_dvd_left hqap _))] at hdvd
      exact hqb (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
    ·
      have hqa : ¬q ∣ P.a := fun ha =>
        hq.not_unit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqbp : q ∣ P.b ^ P.p := dvd_pow hb P.hp0
      rw [c₄Int, add_assoc, dvd_add_left (dvd_add (dvd_mul_of_dvd_right hqbp _)
        (dvd_pow hqbp two_ne_zero))] at hdvd
      exact hqa (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
  ·
    have hqa : ¬q ∣ P.a := fun ha =>
      hq.not_unit (isUnit_of_dvd_one (P.hgcdac ▸ dvd_gcd ha hc))
    have hqb : ¬q ∣ P.b := fun hb =>
      hq.not_unit (isUnit_of_dvd_one (P.hgcdbc ▸ dvd_gcd hb hc))
    rw [c₄Int_eq_sub, dvd_sub_right (dvd_pow (dvd_pow hc P.hp0) two_ne_zero)] at hdvd
    rcases hq.dvd_mul.mp (hq.dvd_of_dvd_pow hdvd) with h | h
    exacts [hqa h, hqb h]

theorem freyCurveInt_c₄ (P : FreyPackage) : (freyCurveInt P).c₄ = c₄Int P := by
  have h : (algebraMap ℤ ℚ) (freyCurveInt P).c₄ = ((c₄Int P : ℤ) : ℚ) := by
    rw [← map_c₄, freyCurveInt_map, ← freyCurve_c₄_eq_intCast]
  rw [eq_intCast] at h
  exact_mod_cast h

theorem freyCurveInt_Δ_mul (P : FreyPackage) :
    (freyCurveInt P).Δ * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have hΔ : (algebraMap ℤ ℚ) (freyCurveInt P).Δ
      = (P.a * P.b * P.c : ℚ) ^ (2 * P.p) / 2 ^ 8 := by
    rw [← map_Δ, freyCurveInt_map, freyCurve_Δ]
  rw [eq_intCast] at hΔ
  have h : ((((freyCurveInt P).Δ * 2 ^ 8 : ℤ)) : ℚ)
      = (((P.a * P.b * P.c) ^ (2 * P.p) : ℤ) : ℚ) := by
    push_cast
    rw [hΔ]
    field_simp
    norm_num
  exact_mod_cast h

theorem freyCurveInt_Δ_ne_zero (P : FreyPackage) : (freyCurveInt P).Δ ≠ 0 := by
  intro h
  have := freyCurveInt_Δ_mul P
  rw [h, zero_mul] at this
  exact pow_ne_zero _ P.habc0 this.symm

theorem dvd_abc_of_dvd_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hdvd : (q : ℤ) ∣ (freyCurveInt P).Δ) : (q : ℤ) ∣ P.a * P.b * P.c := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  exact hqZ.dvd_of_dvd_pow (n := 2 * P.p)
    (freyCurveInt_Δ_mul P ▸ hdvd.mul_right (2 ^ 8))

theorem padicValInt_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q (freyCurveInt P).Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq28 : ¬ (q : ℤ) ∣ 2 ^ 8 := by
    intro h
    have h2 : (q : ℤ) ∣ 2 := hqZ.dvd_of_dvd_pow h
    have h2' : q ∣ 2 := by exact_mod_cast h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2')
  have hmul : padicValInt q ((freyCurveInt P).Δ * 2 ^ 8) = padicValInt q (freyCurveInt P).Δ := by
    rw [padicValInt.mul (freyCurveInt_Δ_ne_zero P) (by norm_num),
      padicValInt.eq_zero_of_not_dvd hq28, add_zero]
  rw [← hmul, freyCurveInt_Δ_mul]
  simp only [padicValInt, Int.natAbs_pow]
  exact padicValNat.pow _ _

end FreyArith

theorem solution (P : FreyPackage) : P.freyCurveInt.Δ ≠ 0 :=
  FreyArith.freyCurveInt_Δ_ne_zero P

end S_FreyPackage_freyCurveInt_discr_ne_zero
end P2MW
export P2MW.S_FreyPackage_freyCurveInt_discr_ne_zero (solution)
