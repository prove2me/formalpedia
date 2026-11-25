-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.cF_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:47.550898+00:00
-- url     : https://prove2.me/submissions/8bee64c8-cfc7-4e5b-887a-dc37ccf3e8fc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_term_bound
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cF_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cS_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
private theorem hH_eq_harmonic' (k : ℕ) : hH k = ((harmonic k : ℚ) : ℝ) := by
  unfold hH
  rw [harmonic_eq_sum_Icc,
    show Finset.Ioc 0 k = Finset.Icc 1 k by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega]
  push_cast
  rfl
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
end
end

set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (hχ : χ ≠ 1) (N U : ℕ) (hU : 1 ≤ U) (hUN : U * U ≤ N) :
    ‖cF χ N - (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U)‖ ≤
      2 * U / N + 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by
  have hUle : U ≤ N := le_trans (Nat.le_mul_of_pos_left U (by omega)) hUN
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  rw [cF_split χ N U hUle]
  have hX : (((Real.log N + Real.eulerMascheroniConstant : ℝ) : ℂ) * cS χ U - cT χ U) =
      ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) *
        (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ) := by
    unfold cS cT
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  rw [hX]
  have hre : ∀ A B C : ℂ, A + B - C = (A - C) + B := fun A B C => by ring
  rw [hre, ← Finset.sum_sub_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ b ∈ Ioc 0 U, ‖χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) - χ (b : ZMod q) / (b : ℂ) *
          (((Real.log N + Real.eulerMascheroniConstant - Real.log b : ℝ)) : ℂ)‖
        ≤ ∑ b ∈ Ioc 0 U, 2 / (N : ℝ) := by
          apply Finset.sum_le_sum
          intro b hb
          rw [Finset.mem_Ioc] at hb
          have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.1
          rw [← mul_sub, norm_mul, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_natCast]
          have h1 := term_bound N U b hb.1 hb.2 hUN
          have h2 : ‖χ (b : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
          calc ‖χ (b : ZMod q)‖ / b * |hH (N / b) - (Real.log N + Real.eulerMascheroniConstant - Real.log b)|
              ≤ 1 / b * (2 * b / N) := by gcongr
            _ = 2 / N := by field_simp
      _ = 2 * U / N := by simp; ring
  · have htail : ∀ a ∈ Ioc 0 N, ‖∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖ ≤ 8 * ((q : ℝ) + 1) / U := by
      intro a ha
      by_cases hM : N / a ≤ U
      · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        positivity
      · push_neg at hM
        have hsplit : ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) = cS χ (N / a) - cS χ U := by
          unfold cS
          rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hM.le]
          ring
        rw [hsplit]
        have h1 := cS_approx χ hχ U hU
        have h2 := cS_approx χ hχ (N / a) (by omega)
        have hMR : (U : ℝ) ≤ ((N / a : ℕ) : ℝ) := by exact_mod_cast hM.le
        have h3 : 4 * ((q : ℝ) + 1) / ((N / a : ℕ) : ℝ) ≤ 4 * ((q : ℝ) + 1) / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 hMR
        calc ‖cS χ (N / a) - cS χ U‖ = ‖(DirichletCharacter.LFunction χ 1 - cS χ U) -
              (DirichletCharacter.LFunction χ 1 - cS χ (N / a))‖ := by
              congr 1
              ring
          _ ≤ ‖DirichletCharacter.LFunction χ 1 - cS χ U‖ +
              ‖DirichletCharacter.LFunction χ 1 - cS χ (N / a)‖ := norm_sub_le _ _
          _ ≤ 4 * ((q : ℝ) + 1) / U + 4 * ((q : ℝ) + 1) / U := add_le_add h1 (h2.trans h3)
          _ = 8 * ((q : ℝ) + 1) / U := by ring
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a ∈ Ioc 0 N, ‖((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ)‖
        ≤ ∑ a ∈ Ioc 0 N, ((a : ℝ))⁻¹ * (8 * ((q : ℝ) + 1) / U) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (htail a ha) (by positivity)
      _ = hH N * (8 * ((q : ℝ) + 1) / U) := by rw [hH, Finset.sum_mul]
      _ ≤ (1 + Real.log N) * (8 * ((q : ℝ) + 1) / U) := by
          have hh : hH N ≤ 1 + Real.log N := by
            rw [hH_eq_harmonic']
            exact harmonic_le_one_add_log N
          exact mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 8 * ((q : ℝ) + 1) * (1 + Real.log N) / U := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
