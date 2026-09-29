-- Prove2me | solution 1 for GaloisRep.isLocalization_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f3dc8a19-1101-5493-8894-2dcd7a1143e4

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_isLocalization_ratLocalizedAt

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
namespace FlatSol
p2m_open "GaloisRep"

theorem mem_ratLocalizedAt_iff_coprime {p : ℕ} (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ q.den.Coprime p :=
  Iff.rfl

theorem mem_ratLocalizedAt_iff {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ ¬ p ∣ q.den := by
  rw [mem_ratLocalizedAt_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem ratLocalizedAt.isUnit_iff {p : ℕ} (hp : p.Prime) (x : ratLocalizedAt p) :
    IsUnit x ↔ ¬ p ∣ (x : ℚ).num.natAbs := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have hxy : (x : ℚ) * y = 1 := by
      rw [← Subring.coe_mul, hy, Subring.coe_one]
    have hx0 : (x : ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hxy
    have hyden : ¬ p ∣ (y : ℚ).den := (mem_ratLocalizedAt_iff hp _).mp y.2
    rwa [eq_inv_of_mul_eq_one_right hxy, Rat.den_inv_of_ne_zero hx0] at hyden
  · intro hx
    have hx0 : (x : ℚ) ≠ 0 := by
      intro h0
      apply hx
      rw [h0, Rat.zero_num, Int.natAbs_zero]
      exact dvd_zero p
    have hmem : (x : ℚ)⁻¹ ∈ ratLocalizedAt p := by
      rw [mem_ratLocalizedAt_iff hp, Rat.den_inv_of_ne_zero hx0]
      exact hx
    exact IsUnit.of_mul_eq_one ⟨(x : ℚ)⁻¹, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hx0))

theorem isLocalization_ratLocalizedAt {p : ℕ} (hp : p.Prime) [(Ideal.span {(p : ℤ)}).IsPrime] :
    IsLocalization.AtPrime (ratLocalizedAt p) (Ideal.span {(p : ℤ)}) := by
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  ·
    have hy : ¬ (p : ℤ) ∣ (y : ℤ) := fun h =>
      Ideal.mem_primeCompl_iff.mp y.2 (Ideal.mem_span_singleton.mpr h)
    refine (ratLocalizedAt.isUnit_iff hp _).mpr fun h => hy (Int.natCast_dvd.mpr ?_)
    rwa [show ((algebraMap ℤ (ratLocalizedAt p) (y : ℤ) : ratLocalizedAt p) : ℚ) = ((y : ℤ) : ℚ)
      from rfl, Rat.num_intCast] at h
  ·
    have hden : ¬ (p : ℤ) ∣ ((z : ℚ).den : ℤ) := fun h =>
      (mem_ratLocalizedAt_iff hp _).mp z.2 (Int.natCast_dvd_natCast.mp h)
    refine ⟨((z : ℚ).num, ⟨((z : ℚ).den : ℤ), Ideal.mem_primeCompl_iff.mpr fun h =>
      hden (Ideal.mem_span_singleton.mp h)⟩), Subtype.ext ?_⟩
    show (z : ℚ) * (((z : ℚ).den : ℤ) : ℚ) = (((z : ℚ).num : ℤ) : ℚ)
    rw [Int.cast_natCast, Rat.mul_den_eq_num]
  ·
    refine ⟨1, ?_⟩
    have h : ((x : ℤ) : ℚ) = ((y : ℤ) : ℚ) := congrArg Subtype.val hxy
    rw [Int.cast_inj.mp h]

end GaloisRep.FlatSol

theorem solution
    {p : ℕ} (hp : p.Prime) [(Ideal.span {(p : ℤ)}).IsPrime] :
    IsLocalization.AtPrime (GaloisRep.ratLocalizedAt p) (Ideal.span {(p : ℤ)}) :=
  GaloisRep.FlatSol.isLocalization_ratLocalizedAt hp

end S_GaloisRep_isLocalization_ratLocalizedAt
end P2MW
export P2MW.S_GaloisRep_isLocalization_ratLocalizedAt (solution)
