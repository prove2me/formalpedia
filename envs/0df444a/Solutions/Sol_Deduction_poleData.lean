-- Prove2me | solution 1 for Deduction.poleData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:25:02.399906+00:00
-- url     : https://prove2.me/submissions/160094c0-aaa8-4480-a151-6c409c109455

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LogDerivLocal
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_CharFamilyLFunctionNeZeroOfOneLeRe
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiModOne
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_measurableGchi
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiGrowth
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_poleData
import Theorems.Thm_Deduction_poleData_integrable
import Theorems.Thm_Deduction_poleData_char
import Theorems.Thm_Deduction_poleData_inv_zero
import Theorems.Thm_Deduction_Gchi_conj
import Theorems.Thm_Deduction_Gchi_growth
import Theorems.Thm_Deduction_charFamily_LFunction_ne_zero_of_one_le_re
import Theorems.Thm_Deduction_measurable_Gchi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (F : CharFamily) : ∃ Φ : ℂ → ℂ, PoleData (gm F) Φ (zeroSet F) := by
  classical
  have adm' : ∀ i, F.N i = 1 ∨ (F.χ i)⁻¹ ≠ 1 := fun i => (F.adm i).imp id (fun h => inv_ne_one.mpr h)
  choose Φ1 hΦ1int hΦ1an hΦ1pol hΦ1iso using fun i => poleData_char (F.χ i) (F.adm i)
  choose Φ2 hΦ2int hΦ2an hΦ2pol hΦ2iso using fun i => poleData_char (F.χ i)⁻¹ (adm' i)
  choose C hC using fun i => Gchi_growth (F.χ i)
  have hZ : ∀ ρ, ρ ∈ zeroSet F ↔ 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
      DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0 := by
    intro ρ
    rw [zeroSet.eq_1]
    rfl
  have hconj : ∀ i (w : ℂ), DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) w) = 0 ↔
      DirichletCharacter.LFunction (F.χ i)⁻¹ w = 0 := fun i w => (poleData_inv_zero (F.χ i) w).symm
  refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s), ?_⟩
  refine PoleData.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hg : gm F = fun u => ∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re := by
      funext u
      rw [gm.eq_1, Gm.eq_1]
    rw [hg]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Complex.measurable_re.comp ((measurable_Gchi (F.χ i)).comp Real.measurable_exp))
  · refine ⟨∑ i, F.a i * C i, fun u hu => ?_⟩
    rw [gm.eq_1, Gm.eq_1]
    have hy : 1 ≤ Real.exp u := Real.one_le_exp hu
    have he : Real.exp u ^ 2 = Real.exp (2 * u) := by
      rw [sq, ← Real.exp_add, two_mul]
    calc |∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re|
        ≤ ∑ i, |F.a i * (Gchi (F.χ i) (Real.exp u)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, F.a i * (C i * Real.exp (2 * u)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (F.a_pos i)]
        apply mul_le_mul_of_nonneg_left _ (F.a_pos i).le
        calc |(Gchi (F.χ i) (Real.exp u)).re| ≤ ‖Gchi (F.χ i) (Real.exp u)‖ := Complex.abs_re_le_norm _
          _ ≤ C i * Real.exp u ^ 2 := hC i _ hy
          _ = C i * Real.exp (2 * u) := by rw [he]
      _ = (∑ i, F.a i * C i) * Real.exp (2 * u) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  · intro s hs
    have hpt : ∀ u : ℝ, ((gm F u : ℝ) : ℂ) * cexp (-s * u) = ∑ i, (F.a i : ℂ) / 2 *
        (Gchi (F.χ i) (Real.exp u) * cexp (-s * u) + Gchi (F.χ i)⁻¹ (Real.exp u) * cexp (-s * u)) := by
      intro u
      rw [gm.eq_1, Gm.eq_1]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_eq_add_conj, Gchi_conj]
      ring
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_add (poleData_integrable _ s hs) (poleData_integrable _ s hs),
        hΦ1int i s hs, hΦ2int i s hs]
    · intro i _
      exact ((poleData_integrable _ s hs).add (poleData_integrable _ s hs)).const_mul _
  · intro ρ hρ
    exact ((hZ ρ).1 hρ).1
  · intro s hs
    obtain ⟨hsre, hsZ⟩ := hs
    have hsre' : 0 < s.re := hsre
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre'; simp at hsre'
    have hL : ∀ i, DirichletCharacter.LFunction (F.χ i) s ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ s ≠ 0 := by
      intro i
      constructor
      · intro h
        exact hsZ ((hZ s).2 ⟨hsre', i, Or.inl h⟩)
      · intro h
        exact hsZ ((hZ s).2 ⟨hsre', i, Or.inr ((hconj i s).2 h)⟩)
    apply DifferentiableAt.differentiableWithinAt
    have han : AnalyticAt ℂ (fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s)) s := by
      apply Finset.analyticAt_fun_sum
      intro i _
      exact analyticAt_const.mul ((hΦ1an i s hs0 (hL i).1).add (hΦ2an i s hs0 (hL i).2))
    exact han.differentiableAt
  · intro z _
    have hall : ∀ᶠ w in 𝓝[≠] z, ∀ i, DirichletCharacter.LFunction (F.χ i) w ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ w ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      exact (hΦ1iso i z).and (hΦ2iso i z)
    filter_upwards [hall] with w hw hwZ
    obtain ⟨_, i, hi⟩ := (hZ w).1 hwZ
    rcases hi with hi | hi
    · exact (hw i).1 hi
    · exact (hw i).2 ((hconj i w).1 hi)
  · intro ρ hρ
    obtain ⟨hρre, i0, hi0⟩ := (hZ ρ).1 hρ
    have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρre; simp at hρre
    have hρ1 : ρ ≠ 1 := by
      intro h
      rcases hi0 with h' | h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ (by rw [h]; simp) h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by rw [h]; simp) h'
    choose m1 hm1 h1 hh1an hh1ev using fun i => hΦ1pol i ρ hρ0
    choose m2 hm2 h2 hh2an hh2ev using fun i => hΦ2pol i ρ hρ0
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i) := ⟨_, rfl⟩
    have hS0 : 0 < S := by
      have hpos : 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := by
        apply mul_pos (by linarith [F.a_pos i0])
        have hm1n : (0:ℝ) ≤ m1 i0 := Nat.cast_nonneg _
        have hm2n : (0:ℝ) ≤ m2 i0 := Nat.cast_nonneg _
        rcases hi0 with h | h
        · have hne : m1 i0 ≠ 0 := fun hm => ((hm1 i0).1 hm) h
          have : (1:ℝ) ≤ m1 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
        · have hne : m2 i0 ≠ 0 := fun hm => ((hm2 i0).1 hm) ((hconj i0 ρ).1 h)
          have : (1:ℝ) ≤ m2 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
      rw [hS]
      calc 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := hpos
        _ ≤ ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i) :=
          Finset.single_le_sum (f := fun i => F.a i / 2 * ((m1 i : ℝ) + m2 i))
            (fun i _ => by have := F.a_pos i; positivity) (Finset.mem_univ i0)
    refine ⟨(S : ℂ) * (-1 / (ρ * (ρ - 1))), ?_, ?_, ?_⟩
    · have hr0 : (-1 / (ρ * (ρ - 1)) : ℂ) ≠ 0 :=
        div_ne_zero (by norm_num) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))
      exact mul_ne_zero (by exact_mod_cast hS0.ne') hr0
    · intro him
      have hρx : ρ = (ρ.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hlt : ρ.re < 1 := by
        by_contra hge
        push_neg at hge
        rcases hi0 with h' | h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ hge h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by simpa using hge) h'
      have hc : (S : ℂ) * (-1 / (ρ * (ρ - 1))) = ((S * (-1 / (ρ.re * (ρ.re - 1))) : ℝ) : ℂ) := by
        push_cast
        rw [← hρx]
      rw [hc, Complex.ofReal_re, Complex.ofReal_im]
      refine ⟨?_, rfl⟩
      have hneg : ρ.re * (ρ.re - 1) < 0 := mul_neg_of_pos_of_neg hρre (by linarith)
      exact mul_pos hS0 (div_pos_of_neg_of_neg (by norm_num) hneg)
    · refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (h1 i s + h2 i s), ?_, ?_⟩
      · apply Finset.analyticAt_fun_sum
        intro i _
        exact analyticAt_const.mul ((hh1an i).add (hh2an i))
      · have hev : ∀ᶠ s in 𝓝[≠] ρ, ∀ i,
            Φ1 i s = (m1 i : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h1 i s ∧
            Φ2 i s = (m2 i : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h2 i s := by
          rw [Filter.eventually_all]
          intro i
          exact (hh1ev i).and (hh2ev i)
        filter_upwards [hev] with s hs
        rw [hS]
        push_cast
        rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hs i).1, (hs i).2]
        ring
end Deduction
