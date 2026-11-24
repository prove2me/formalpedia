-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:19.836111+00:00
-- url     : https://prove2.me/submissions/497ede14-2e2a-47d3-9e70-26d595c575ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_altE_theta
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_quadratic_form_theta_scaling
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_semi
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_half_notMem
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_gen
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_q_odd
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_th0Char_sq
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_altEInt
import Theorems.Thm_Formalism_L2_Th1_H_cayleyGaussianIntegrals_self_fact
import Theorems.Thm_Formalism_L2_Th1_H_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_H_neg_one_zpow_pm
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_add
import Theorems.Thm_Formalism_L2_Th1_H_th0Char_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution (hd : d % 8 = 7) (w : ℂ) (hw : w ∈ L.lattice) : aa L d w = thetaZeroCharacter L ω₀ w := by
  obtain ⟨hq, hpm, hadd⟩ := semi hst
  obtain ⟨Q, hodd, hQ⟩ := q_odd hst h0 hθ hθ'
  have hu : cmTheta 1 d * ω₀ ∈ L.lattice := hst _ h0
  have radd : ∀ x ∈ L.lattice, ∀ y ∈ L.lattice,
      aa L d (x + y) * thetaZeroCharacter L ω₀ (x + y) = (aa L d x * thetaZeroCharacter L ω₀ x) * (aa L d y * thetaZeroCharacter L ω₀ y) := by
    intro x hx y hy
    rw [hadd x hx y hy, th0Char_add L ω₀ x y hx hy]
    obtain ⟨k, hk⟩ := Formalism.L2.Th1.F.altEInt L x y hx hy
    rw [hk, exp_pi_int]
    rcases neg_one_zpow_pm k with h | h <;> rw [h] <;> ring
  have rsq : ∀ x ∈ L.lattice, (aa L d x * thetaZeroCharacter L ω₀ x) * (aa L d x * thetaZeroCharacter L ω₀ x) = 1 := by
    intro x hx
    have h1 := th0Char_sq L ω₀ x h0 hx
    have h2 : aa L d x * aa L d x = 1 := by rcases hpm x hx with h | h <;> rw [h] <;> norm_num
    calc _ = (aa L d x * aa L d x) * (thetaZeroCharacter L ω₀ x * thetaZeroCharacter L ω₀ x) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have rtwo : ∀ v ∈ L.lattice, aa L d (2 * v) * thetaZeroCharacter L ω₀ (2 * v) = 1 := by
    intro v hv; rw [two_mul, radd v hv v hv, rsq v hv]
  have r0 : aa L d ω₀ * thetaZeroCharacter L ω₀ ω₀ = 1 := by
    rw [aa, hQ, exp_pi_int, hodd.neg_one_zpow, thetaZeroCharacter, semiChar, if_neg (half_notMem hst h0 hθ hθ'), cayleyGaussianIntegrals_self_fact]
    simp
  have ru : aa L d (cmTheta 1 d * ω₀) * thetaZeroCharacter L ω₀ (cmTheta 1 d * ω₀) = 1 := by
    have hne : cmTheta 1 d * ω₀ / 2 ∉ L.lattice := by rwa [mul_div_assoc]
    obtain ⟨k', hk'⟩ : ∃ k' : ℤ, (d : ℤ) = 8 * k' + 7 := ⟨(d : ℤ) / 8, by omega⟩
    have hq2 : q1 L d (cmTheta 1 d * ω₀) = (((2 * (k' + 1) * Q : ℤ)) : ℝ) := by
      rw [quadratic_form_theta_scaling, hQ]
      have hd' : (d : ℝ) = 8 * (k' : ℝ) + 7 := by exact_mod_cast hk'
      rw [hd']; push_cast; ring
    rw [aa, hq2, exp_pi_int, thetaZeroCharacter, semiChar, if_neg hne, altE_theta, hQ, exp_pi_int, hodd.neg_one_zpow,
      Even.neg_one_zpow ⟨(k' + 1) * Q, by ring⟩]
    norm_num
  have rall : aa L d w * thetaZeroCharacter L ω₀ w = 1 := by
    obtain ⟨v, hv, hc⟩ := gen hst h0 hθ hθ' w hw
    have h2v : 2 * v ∈ L.lattice := by rw [two_mul]; exact add_mem hv hv
    rcases hc with rfl | rfl | rfl | rfl
    · exact rtwo v hv
    · rw [radd _ h0 _ h2v, r0, rtwo v hv, one_mul]
    · rw [radd _ hu _ h2v, ru, rtwo v hv, one_mul]
    · rw [radd _ (add_mem h0 hu) _ h2v, radd _ h0 _ hu, r0, ru, rtwo v hv]; norm_num
  calc aa L d w = aa L d w * (thetaZeroCharacter L ω₀ w * thetaZeroCharacter L ω₀ w) := by rw [th0Char_sq L ω₀ w h0 hw, mul_one]
    _ = (aa L d w * thetaZeroCharacter L ω₀ w) * thetaZeroCharacter L ω₀ w := by ring
    _ = thetaZeroCharacter L ω₀ w := by rw [rall, one_mul]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
