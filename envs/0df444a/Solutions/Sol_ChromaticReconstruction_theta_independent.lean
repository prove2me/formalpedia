-- Prove2me | solution 1 for ChromaticReconstruction.theta_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:36.685572+00:00
-- url     : https://prove2.me/submissions/36fb3d19-f52c-483b-ab98-ad9e25db62ab

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_coeff_thetaAB_eq_zero
import Theorems.Thm_ChromaticReconstruction_coeff_thetaAB_self_pos
import Theorems.Thm_ChromaticReconstruction_sum_map_eq_sum_count
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) (E1 E2 : Multiset (Sym2 ℕ))
    (hf : ∀ z ∈ E1 + E2, pairMS z ≤ W)
    (h : (E1.map (theta W)).sum = (E2.map (theta W)).sum) : E1 = E2 := by
  by_contra hne
  set S := (E1 + E2).toFinset
  set D : Sym2 ℕ → ℤ := fun z => (E1.count z : ℤ) - E2.count z
  set T := S.filter fun z => D z ≠ 0
  have hT : T.Nonempty := by
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    apply hne
    ext z
    by_cases hz : z ∈ S
    · have : z ∉ T := by rw [hT]; exact notMem_empty z
      simp only [T, mem_filter, not_and, not_not] at this
      have := this hz
      simp only [D] at this
      omega
    · simp only [S, Multiset.mem_toFinset, Multiset.mem_add, not_or] at hz
      rw [Multiset.count_eq_zero_of_notMem hz.1, Multiset.count_eq_zero_of_notMem hz.2]
  obtain ⟨z0, hz0T, hmin⟩ := exists_min_image T pairSum hT
  have hz0S : z0 ∈ S := (mem_filter.1 hz0T).1
  have hD0 : D z0 ≠ 0 := (mem_filter.1 hz0T).2
  induction z0 using Sym2.ind with
  | _ a b =>
  have hab : {a, b} ≤ W := pairMS_mk a b ▸ hf s(a, b) (by simpa [S] using hz0S)
  set ν := (a + b - 1) ::ₘ (W - {a, b})
  have hc := congrArg (coeff (Multiset.toFinsupp ν)) h
  rw [sum_map_eq_sum_count E1 S (by
      intro z hz; simp only [S, Multiset.mem_toFinset, Multiset.mem_add] at hz ⊢; exact Or.inl hz),
    sum_map_eq_sum_count E2 S (by
      intro z hz; simp only [S, Multiset.mem_toFinset, Multiset.mem_add] at hz ⊢; exact Or.inr hz),
    coeff_sum, coeff_sum] at hc
  have hc2 : ∑ z ∈ S, ((D z : ℚ) * coeff (Multiset.toFinsupp ν) (theta W z)) = 0 := by
    simp only [D, Int.cast_sub, Int.cast_natCast, sub_mul, sum_sub_distrib]
    have hsm : ∀ (n : ℕ) (p : MvPolynomial ℕ ℚ) (m : ℕ →₀ ℕ),
        coeff m (n • p) = (n : ℚ) * coeff m p := by
      intro n p m
      rw [nsmul_eq_mul, ← map_natCast (C : ℚ →+* MvPolynomial ℕ ℚ), coeff_C_mul]
    simp only [hsm] at hc
    rw [hc, sub_self]
  rw [sum_eq_single s(a, b)] at hc2
  · have hpos := coeff_thetaAB_self_pos hW hab
    rw [theta_mk] at hc2
    have : (D s(a, b) : ℚ) = 0 := by
      rcases mul_eq_zero.1 hc2 with h' | h'
      · exact h'
      · exact absurd h' hpos.ne'
    exact hD0 (by exact_mod_cast this)
  · intro z hzS hz
    by_cases hDz : D z = 0
    · rw [hDz]; simp
    · have hzT : z ∈ T := mem_filter.2 ⟨hzS, hDz⟩
      have hle := hmin z hzT
      induction z using Sym2.ind with
      | _ c d =>
      have hcd : {c, d} ≤ W := pairMS_mk c d ▸ hf s(c, d) (by simpa [S] using hzS)
      rw [theta_mk, coeff_thetaAB_eq_zero hW hab hcd hz (by simpa using hle), mul_zero]
  · intro h'; exact absurd hz0S h'
end ChromaticReconstruction
