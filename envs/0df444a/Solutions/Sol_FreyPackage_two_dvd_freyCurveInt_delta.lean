-- Prove2me | solution 1 for FreyPackage.two_dvd_freyCurveInt_delta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3498a102-97bd-5111-9af9-d3cf52f698de

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_freyCurveInt_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_two_dvd_freyCurveInt_delta

open WeierstrassCurve FreyPackage

private theorem freyCurve_Δ' (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c : ℚ) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p : ℚ) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

private theorem freyCurveInt_Δ_mul' (P : FreyPackage) :
    (freyCurveInt P).Δ * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have hΔ : ((freyCurveInt P).Δ : ℚ)
      = (P.a * P.b * P.c : ℚ) ^ (2 * P.p) / 2 ^ 8 := by
    have h := congrArg WeierstrassCurve.Δ P.freyCurveInt_map
    rw [map_Δ] at h
    simp only [eq_intCast] at h
    rw [h, freyCurve_Δ']
  have h : ((((freyCurveInt P).Δ * 2 ^ 8 : ℤ)) : ℚ)
      = (((P.a * P.b * P.c) ^ (2 * P.p) : ℤ) : ℚ) := by
    push_cast
    rw [hΔ]
    field_simp
    norm_num
  exact_mod_cast h

theorem solution (P : FreyPackage) :
    (2 : ℤ) ∣ (FreyPackage.freyCurveInt P).Δ := by

  have h2b : (2 : ℤ) ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  have h2abc : (2 : ℤ) ^ (2 * P.p) ∣ (P.a * P.b * P.c) ^ (2 * P.p) :=
    pow_dvd_pow_of_dvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2b _) _) _
  rw [← freyCurveInt_Δ_mul' P] at h2abc

  have hp8 : 8 ≤ 2 * P.p := by have := P.hp5; omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp8
  rw [hk, pow_add, mul_comm ((2:ℤ)^8)] at h2abc
  have h2k : (2 : ℤ) ^ k ∣ (freyCurveInt P).Δ :=
    (mul_dvd_mul_iff_right (pow_ne_zero 8 (two_ne_zero))).mp h2abc
  have hk1 : 1 ≤ k := by have := P.hp5; omega
  calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
    _ ∣ 2 ^ k := pow_dvd_pow 2 hk1
    _ ∣ (freyCurveInt P).Δ := h2k

end S_FreyPackage_two_dvd_freyCurveInt_delta
end P2MW
export P2MW.S_FreyPackage_two_dvd_freyCurveInt_delta (solution)
