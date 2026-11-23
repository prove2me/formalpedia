-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.joint_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:00.226701+00:00
-- url     : https://prove2.me/submissions/154a9913-afd5-4656-8c18-4ba1585fa785

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
private lemma gl5t1_count (N : ℕ) (sg : Fin N → Bool) :
    ∑ a, (univ.filter (fun b => a < b ∧ sg a ≠ sg b)).card =
      (univ.filter (fun a => sg a = true)).card * (univ.filter (fun a => sg a = false)).card := by
  classical
  let f1 : Fin N → Fin N → ℕ := fun a b => if a < b ∧ sg a = true ∧ sg b = false then 1 else 0
  let f2 : Fin N → Fin N → ℕ := fun a b => if a < b ∧ sg a = false ∧ sg b = true then 1 else 0
  have hL : ∀ a, (univ.filter (fun b => a < b ∧ sg a ≠ sg b)).card = ∑ b, (f1 a b + f2 a b) := by
    intro a
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [f1, f2]
    cases sg a <;> cases sg b <;> simp
  have hR : (univ.filter (fun a => sg a = true)).card * (univ.filter (fun a => sg a = false)).card =
      ∑ a, ∑ b, (f1 a b + f2 b a) := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [f1, f2]
    rcases lt_trichotomy a b with h | h | h
    · have h' : ¬ b < a := not_lt.mpr h.le
      cases sg a <;> cases sg b <;> simp [h, h']
    · subst h
      cases sg a <;> simp
    · have h' : ¬ a < b := not_lt.mpr h.le
      cases sg a <;> cases sg b <;> simp [h, h']
  rw [hR]
  simp_rw [hL, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : JointLowerBound := by
  intro N lam sg d dτ c ε₀ Z hlam p q nab hd hc he0 he1 hZ hZle hc' hτ h12
  set Fp : ℝ := ∏ i ∈ range p, (i.factorial : ℝ) with hFp
  set Fq : ℝ := ∏ i ∈ range q, (i.factorial : ℝ) with hFq
  set FN : ℝ := ∏ i ∈ range N, (i.factorial : ℝ) with hFN
  have hFp0 : 0 < Fp := Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)
  have hFq0 : 0 < Fq := Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)
  have hFN0 : 0 < FN := Finset.prod_pos (fun i _ => by exact_mod_cast i.factorial_pos)
  set Pc : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b + (nab a b : ℝ)) with hPc
  set Pc0 : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a = sg b), (lam a - lam b) with hPc0
  set Pn : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b),
    (lam a - lam b + ((b.val : ℝ) - a.val)) with hPn
  set Pn0 : ℝ := ∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b), (lam a - lam b) with hPn0
  have hPc0pos : 0 < Pc0 := Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => by
    have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
  have hPn0pos : 0 < Pn0 := Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => by
    have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
  have hPcle : Pc0 ≤ Pc := Finset.prod_le_prod
    (fun a _ => Finset.prod_nonneg (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
    (fun a _ => Finset.prod_le_prod (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith)
      (fun b _ => by
        have : (0 : ℝ) ≤ (nab a b : ℝ) := Nat.cast_nonneg _
        linarith))
  have hPnle : Pn0 ≤ Pn := Finset.prod_le_prod
    (fun a _ => Finset.prod_nonneg (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith))
    (fun a _ => Finset.prod_le_prod (fun b hb => by
      have := hlam a b (Finset.mem_filter.mp hb).2.1; linarith)
      (fun b hb => by
        have h : a < b := (Finset.mem_filter.mp hb).2.1
        have : (a.val : ℝ) ≤ (b.val : ℝ) := by exact_mod_cast h.le
        linarith))
  have hall : (∏ a, ∏ b ∈ univ.filter (fun b => a < b), (lam a - lam b)) = Pc0 * Pn0 := by
    rw [hPc0, hPn0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter (fun b => a < b)) (fun b => sg a = sg b),
      Finset.filter_filter, Finset.filter_filter]
  have hπ : (∏ a, ∏ b ∈ univ.filter (fun b => a < b ∧ sg a ≠ sg b),
      Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))) = Real.pi ^ (p * q) / Pn := by
    simp_rw [Finset.prod_div_distrib, Finset.prod_const]
    rw [Finset.prod_pow_eq_pow_sum, gl5t1_count]
  have hPcpos : 0 < Pc := lt_of_lt_of_le hPc0pos hPcle
  have hPnpos : 0 < Pn := lt_of_lt_of_le hPn0pos hPnle
  have hπpos : 0 < Real.pi ^ (p * q) := pow_pos Real.pi_pos _
  have hceq : c = FN / (Real.pi ^ (p * q) * (Fp * Fq)) := by
    have h1 : c = 1 / (1 / c) := by field_simp
    rw [h1, hc']
    field_simp
  rw [hall]
  rw [hπ, hτ, hceq] at h12
  have e : FN / (Real.pi ^ (p * q) * (Fp * Fq)) / (Pc / (Fp * Fq)) * (Real.pi ^ (p * q) / Pn) * Z =
      FN * Z / (Pc * Pn) := by
    field_simp
  rw [e] at h12
  have h1e : 0 < 1 - ε₀ := by linarith
  have hZ' : (1 - ε₀) * Z ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hZle h1e.le
    rwa [mul_inv_cancel₀ h1e.ne'] at this

  have h2 : Pc * Pn ≤ d * (FN * Z) := by
    rw [div_le_div_iff₀ hd (by positivity)] at h12
    linarith
  have h3 : Pc0 * Pn0 ≤ Pc * Pn := mul_le_mul hPcle hPnle hPn0pos.le hPcpos.le
  rw [← mul_div_assoc, div_le_iff₀ hFN0]
  calc (1 - ε₀) * (Pc0 * Pn0) ≤ (1 - ε₀) * (d * (FN * Z)) :=
        mul_le_mul_of_nonneg_left (h3.trans h2) h1e.le
    _ = (d * FN) * ((1 - ε₀) * Z) := by ring
    _ ≤ (d * FN) * 1 := mul_le_mul_of_nonneg_left hZ' (by positivity)
    _ = d * FN := mul_one _
end Formalism.HermitianLattices.GenusMassVolumes
