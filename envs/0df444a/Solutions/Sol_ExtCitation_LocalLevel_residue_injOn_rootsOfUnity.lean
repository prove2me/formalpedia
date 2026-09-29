-- Prove2me | solution 1 for ExtCitation.LocalLevel.residue_injOn_rootsOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2b38932a-6647-5c44-9905-9841e8639c64

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField ExtCitation.LocalLevel
open Polynomial

theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₁ ζ₂ : Rw q Kw) (h₁ : ζ₁ ^ m = 1) (h₂ : ζ₂ ^ m = 1)
    (h : IsLocalRing.residue (Rw q Kw) ζ₁ = IsLocalRing.residue (Rw q Kw) ζ₂) : ζ₁ = ζ₂ := by
  classical
  have hm0 : m ≠ 0 := fun h0 => hm (h0 ▸ dvd_zero q)
  have hmem : ∀ x : Kw, x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := fun x => by
    change ((x : PadicAlgCl q)) ∈ padicIntegers q ↔ _
    rw [mem_padicIntegers_iff]
    rfl

  have hqmax : ((q : ℕ) : Rw q Kw) ∈ IsLocalRing.maximalIdeal (Rw q Kw) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨v, hv⟩ := hu
    have hvinv : ‖((((v⁻¹ : (Rw q Kw)ˣ) : Rw q Kw) : Kw) : PadicAlgCl q)‖ ≤ 1 := (hmem _).1 ((v⁻¹ : (Rw q Kw)ˣ) : Rw q Kw).2
    have hprod : ((((v : Rw q Kw) : Kw)) : PadicAlgCl q) * ((((v⁻¹ : (Rw q Kw)ˣ) : Rw q Kw) : Kw) : PadicAlgCl q) = 1 := by
      have := congrArg (fun r : Rw q Kw => ((r : Kw) : PadicAlgCl q)) v.mul_inv
      exact this
    have hqnorm : ‖((((v : Rw q Kw) : Kw)) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
      rw [hv]
      change ‖((algebraMap ℚ_[q] (PadicAlgCl q)) (q : ℚ_[q]))‖ = _
      rw [norm_algebraMap', Padic.norm_p]
    have h1 : (1 : ℝ) = ‖((((v : Rw q Kw) : Kw)) : PadicAlgCl q)‖ * ‖((((v⁻¹ : (Rw q Kw)ˣ) : Rw q Kw) : Kw) : PadicAlgCl q)‖ := by
      rw [← norm_mul, hprod, norm_one]
    have hqlt : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)
    have : (1 : ℝ) < 1 := by
      calc (1 : ℝ) = _ := h1
        _ ≤ (q : ℝ)⁻¹ * 1 := by rw [hqnorm]; exact mul_le_mul_of_nonneg_left hvinv (by positivity)
        _ < 1 := by rw [mul_one]; exact hqlt
    exact lt_irrefl _ this

  have hmmax : ((m : ℕ) : Rw q Kw) ∉ IsLocalRing.maximalIdeal (Rw q Kw) := by
    intro hmm
    have hcop : IsCoprime (m : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
    obtain ⟨a, b, hab⟩ := hcop
    have : (1 : Rw q Kw) ∈ IsLocalRing.maximalIdeal (Rw q Kw) := by
      have e : (a : Rw q Kw) * (m : Rw q Kw) + (b : Rw q Kw) * (q : Rw q Kw) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : Rw q Kw)) hab
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmm) (Ideal.mul_mem_left _ _ hqmax)
    exact (IsLocalRing.maximalIdeal.isMaximal (Rw q Kw)).ne_top ((Ideal.eq_top_iff_one _).2 this)

  set u : Rw q Kw := ζ₂ * ζ₁ ^ (m - 1) with hu
  have hum : u ^ m = 1 := by
    rw [hu, mul_pow, ← pow_mul, h₂, one_mul, show (m - 1) * m = m * (m - 1) from mul_comm _ _, pow_mul, h₁, one_pow]
  have hures : IsLocalRing.residue (Rw q Kw) u = 1 := by
    rw [hu, map_mul, map_pow, ← h, ← map_pow, ← map_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), h₁,
      map_one]
  suffices hu1 : u = 1 by
    have : ζ₁ * u = ζ₂ := by
      rw [hu, mul_comm ζ₂, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), h₁, one_mul]
    rw [← this, hu1, mul_one]
  by_contra hne
  have hgeom : (∑ k ∈ Finset.range m, u ^ k) * (u - 1) = 0 := by rw [geom_sum_mul, hum, sub_self]
  have hsum0 : ∑ k ∈ Finset.range m, u ^ k = 0 :=
    (mul_eq_zero.1 hgeom).resolve_right (sub_ne_zero.2 hne)
  have hres : IsLocalRing.residue (Rw q Kw) (∑ k ∈ Finset.range m, u ^ k) = (m : IsLocalRing.ResidueField (Rw q Kw)) := by
    rw [map_sum]
    simp only [map_pow, hures, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [hsum0, map_zero] at hres
  apply hmmax
  rw [← IsLocalRing.residue_eq_zero_iff]
  rw [map_natCast]
  exact hres.symm

end S_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity
end P2MW
export P2MW.S_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity (solution)
