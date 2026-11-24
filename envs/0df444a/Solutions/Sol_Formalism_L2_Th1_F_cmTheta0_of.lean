-- Prove2me | solution 1 for Formalism.L2.Th1.F.cmTheta0_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:04.559526+00:00
-- url     : https://prove2.me/submissions/c1a2c28d-9991-463f-8220-b7fda8514dd0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_FormEvenIff
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_half_mem_iff
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_even_im_hermitian_sub
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_form_even_iff
import Theorems.Thm_Formalism_L2_Th1_F_Cm2_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_PeriodAreaSignLemmas_exp_pi_int
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_exp_pi_int


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Cm1 Cm2
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : ThetaZeroBasic) (hE : CmAltE) : CmTheta0 := by
  intro a b c d ha hd hac hodd hd8 m n z
  have hmem : ∀ p q : ℤ, (p : ℂ) * (a : ℂ) + (q : ℂ) * cmTheta b d ∈ (cmPair a b d ha hd).lattice := by
    intro p q
    have := (half_mem_iff a b d ha hd (2 * p) (2 * q)).2 ⟨even_two_mul p, even_two_mul q⟩
    convert this using 1
    push_cast
    ring
  have ha0 : (a : ℂ) ∈ (cmPair a b d ha hd).lattice := by simpa using hmem 1 0
  have ha2 : (a : ℂ) / 2 ∉ (cmPair a b d ha hd).lattice := by
    intro hh
    have h10 := (half_mem_iff a b d ha hd 1 0).1 (by simpa using hh)
    obtain ⟨r, hr⟩ := h10.1
    omega
  have key := (h (cmPair a b d ha hd) (a : ℂ) ha0 ha2).2.2.2.2 _ (hmem m n) z
  rw [key]
  congr 2
  have hsc : semiChar (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d)
      = if Even m ∧ Even n then 1 else -1 := by
    unfold semiChar
    simp only [half_mem_iff a b d ha hd m n]
  have hA : altE (cmPair a b d ha hd) ((m : ℂ) * (a : ℂ) + (n : ℂ) * cmTheta b d) (a : ℂ) = (n : ℝ) := by
    have h1 := hE a b d ha hd m n 1 0
    have e : ((1 : ℤ) : ℂ) * (a : ℂ) + ((0 : ℤ) : ℂ) * cmTheta b d = (a : ℂ) := by
      push_cast
      ring
    rw [e] at h1
    rw [h1]
    push_cast
    ring
  obtain ⟨hbo, hce⟩ := even_im_hermitian_sub a b c d hac hodd hd8
  have hao : Odd (a : ℤ) := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t, by rw [ht]; push_cast; ring⟩
  have hpar := form_even_iff a b c m n hao hbo hce
  have hpow : ((-1 : ℂ)) ^ (cmForm a b c m n).natAbs = if Even (cmForm a b c m n) then 1 else -1 := by
    split_ifs with hk
    · exact (Int.natAbs_even.mpr hk).neg_one_pow
    · exact (Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hk)).neg_one_pow
  rw [hsc, hA, exp_pi_int, hpow]
  simp only [hpar]
  by_cases hm : Even m <;> by_cases hn : Even n <;> simp [hm, hn, ← Int.not_even_iff_odd]
end Formalism.L2.Th1.F
