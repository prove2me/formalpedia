-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.act_unit_pi0_eq_mul_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:55.09513+00:00
-- url     : https://prove2.me/submissions/ce41adbd-d5f1-4059-9ad3-8f08a064cd07

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_algHom_C_eq
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_prod_sub_prod
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_one_add_pow_eq_linear_add_sq_mul
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_br_eq_X_mul_const_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0_eq_zero_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_inc_pi0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_act
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_inc
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeriesSubOne_add_prime_mul_cong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hi : DivisibilityInvariant) (hf : RootsOfUnityInvariants) (h4 : R4)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (u c : ℤ_[l]) (hu : u = 1 + (l : ℤ_[l]) * c) :
    ∃ un : ℤ_[l]⟦X⟧,
      act l ℤ_[l] u (pi0 l ℤ_[l]) = pi0 l ℤ_[l] * (1 + inc l ℤ_[l] un * q0 l ℤ_[l]) ∧
      ∃ e : ℤ_[l], constantCoeff un = c + (l : ℤ_[l]) * e := by
  classical
  obtain ⟨hcard, -, hprod⟩ := hm l
  have hprod := hprod hl
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  choose β hβ hβ0 using br_eq_X_mul_const_alt l ℤ_[l]
  obtain ⟨a1, a2, -, -, -, a6, -⟩ := ha l ℤ_[l]
  obtain ⟨B, hB⟩ : ∃ B, B = ∏ d ∈ mu l, β d := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = ∏ d ∈ mu l, β (d * u) := ⟨_, rfl⟩
  have hP : pi0 l ℤ_[l] = X ^ (l - 1) * B := by
    rw [pi0, hB, ← hcard, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun d _ => hβ d
  have hact : act l ℤ_[l] u (pi0 l ℤ_[l]) = X ^ (l - 1) * B' := by
    obtain ⟨Φ, hΦ⟩ := exists_algHom_act l ℤ_[l] u
    have h0 : act l ℤ_[l] u (pi0 l ℤ_[l]) = ∏ d ∈ mu l, br l ℤ_[l] (d * u) := by
      rw [hΦ, pi0, map_prod]
      refine prod_congr rfl fun d _ => ?_
      rw [← hΦ]
      exact a1 u d
    rw [h0, hB', ← hcard, ← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun d _ => hβ _
  have hB0 : constantCoeff B = -1 := by
    rw [hB, map_prod, ← hprod]
    exact prod_congr rfl fun d _ => by rw [hβ0]; rfl
  have hB'0 : constantCoeff B' = -u ^ (l - 1) := by
    rw [hB', map_prod]
    have h0 : ∀ d ∈ mu l, constantCoeff (β (d * u)) = d * u := fun d _ => by rw [hβ0]; rfl
    rw [prod_congr rfl h0, prod_mul_distrib, prod_const, hprod, hcard]
    ring
  have hBu : IsUnit B := isUnit_iff_constantCoeff.mpr (by rw [hB0]; exact isUnit_one.neg)
  obtain ⟨Bi, hBi⟩ := hBu.exists_right_inv
  obtain ⟨r, hrdef⟩ : ∃ r, r = B' * Bi := ⟨_, rfl⟩
  have hr : act l ℤ_[l] u (pi0 l ℤ_[l]) = pi0 l ℤ_[l] * r := by
    rw [hact, hP, hrdef]
    linear_combination (-(X ^ (l - 1) * B')) * hBi
  have hQ : q l ℤ_[l] ∣ B' - B := by
    rw [hB', hB]
    refine dvd_prod_sub_prod _ _ _ _ fun d _ => ?_
    obtain ⟨s, hs⟩ := binomialSeriesSubOne_add_prime_mul_cong l ℤ_[l] ha hq d (d * c)
    have hdu : d * u = d + d * c * (l : ℤ_[l]) := by rw [hu]; ring
    rw [← hdu, hβ, hβ] at hs
    have h0 : X * (β (d * u) - β d) = X * (q l ℤ_[l] * s) := by linear_combination hs
    exact ⟨s, mul_left_cancel₀ X_ne_zero h0⟩
  have hQr : q l ℤ_[l] ∣ r - 1 := by
    have h0 : r - 1 = (B' - B) * Bi := by rw [hrdef]; linear_combination hBi
    rw [h0]
    exact Dvd.dvd.mul_right hQ _
  have hP0 : pi0 l ℤ_[l] ≠ 0 := by
    rw [hP]
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) hBu.ne_zero
  have hinv : ∀ d ∈ mu l, act l ℤ_[l] d r = r := by
    intro d hd
    have e1 : act l ℤ_[l] d (act l ℤ_[l] u (pi0 l ℤ_[l])) = act l ℤ_[l] u (pi0 l ℤ_[l]) := by
      rw [a2, mul_comm, ← a2, hi l ℤ_[l] d hd]
    rw [hr, (a6 d _ _).1, hi l ℤ_[l] d hd] at e1
    exact mul_left_cancel₀ hP0 e1
  obtain ⟨ρ, hρ⟩ := (hf l ℤ_[l] hl r).mp hinv
  obtain ⟨Φ, hΦ, hΦX⟩ := exists_algHom_inc_pi0 l ℤ_[l] hm
  obtain ⟨y, hy⟩ := hQr
  obtain ⟨un, hun⟩ := h4 l ℤ_[l] hl 1 (ρ - 1) y (by
    rw [hΦ, map_sub, map_one, ← hΦ, ← hρ, hy, pow_one])
  have hrr : r = 1 + inc l ℤ_[l] un * q0 l ℤ_[l] := by
    have h0 : ρ = 1 + (X - C (l : ℤ_[l])) * un := by
      rw [pow_one] at hun
      linear_combination hun
    rw [hρ, hΦ ρ, h0, map_add, map_one, map_mul, map_sub, hΦX, algHom_C_eq, ← hΦ, q0]
    ring
  refine ⟨un, by rw [hr, hrr], ?_⟩

  have hBi0 : constantCoeff Bi = -1 := by
    have h0 := congrArg constantCoeff hBi
    rw [map_mul, hB0, map_one] at h0
    linear_combination -h0
  have hr0 : constantCoeff r = u ^ (l - 1) := by
    rw [hrdef, map_mul, hB'0, hBi0]
    ring
  have hq00 : constantCoeff (q0 l ℤ_[l]) = -(l : ℤ_[l]) := by
    rw [q0, map_sub, constantCoeff_pi0_eq_zero_alt l ℤ_[l] hm, constantCoeff_C, zero_sub]
  have hmain : u ^ (l - 1) = 1 + constantCoeff un * (-(l : ℤ_[l])) := by
    have h0 := congrArg constantCoeff hrr
    rw [hr0, map_add, map_one, map_mul, constantCoeff_inc l ℤ_[l] hm, hq00] at h0
    exact h0
  obtain ⟨e, he⟩ := one_add_pow_eq_linear_add_sq_mul ((l : ℤ_[l]) * c) (l - 1)
  have hn : ((l - 1 : ℕ) : ℤ_[l]) = (l : ℤ_[l]) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hu, he, hn] at hmain
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  refine ⟨-c - c ^ 2 * e, ?_⟩
  have h0 : (l : ℤ_[l]) * constantCoeff un = (l : ℤ_[l]) * (c + (l : ℤ_[l]) * (-c - c ^ 2 * e)) := by
    linear_combination hmain
  exact mul_left_cancel₀ hl0 h0
end Formalism.CohomologicalDescent.HeightDescentMinors
