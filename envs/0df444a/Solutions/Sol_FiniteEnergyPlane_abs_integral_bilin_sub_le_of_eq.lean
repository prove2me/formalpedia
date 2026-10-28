-- Prove2me | solution 1 for FiniteEnergyPlane.abs_integral_bilin_sub_le_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T23:04:16.740405+00:00
-- url     : https://prove2.me/submissions/09908180-70d9-47ed-bcec-403ada09d744

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-- Bound for the boundary term of a closed curve. -/
theorem abs_integral_bilin_sub_le_of_eq_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (σ : F →L[ℝ] F →L[ℝ] ℝ) {γ γ' : ℝ → F} {a b : ℝ}
    (hab : a ≤ b) (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hper : γ a = γ b) (q : F) :
    |∫ t in a..b, σ (γ t - q) (γ' t)| ≤ ‖σ‖ * (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 := by
  have sq_integral_le : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc a b) →
      (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
    intro g hg
    rcases hab.eq_or_lt with h | hlt
    · subst h; simp
    have hba : 0 < b - a := by linarith
    have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab
    have hg2i : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
      (hg.pow 2).intervalIntegrable_of_Icc hab
    set L := ∫ t in a..b, g t
    set m := L / (b - a)
    have h0 : 0 ≤ ∫ t in a..b, (g t - m) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
    have hexp : ∫ t in a..b, (g t - m) ^ 2 =
        (∫ t in a..b, g t ^ 2) - 2 * m * L + m ^ 2 * (b - a) := by
      have e : (fun t => (g t - m) ^ 2) = fun t => (g t ^ 2 - (2 * m) * g t) + m ^ 2 := by
        funext t; ring
      rw [e, intervalIntegral.integral_add (hg2i.sub (hgi.const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub hg2i (hgi.const_mul _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [hexp] at h0
    have hm : m * (b - a) = L := by simp only [m]; field_simp
    have : L ^ 2 = m ^ 2 * (b - a) * (b - a) := by rw [← hm]; ring
    nlinarith
  have hγc : ContinuousOn γ (Icc a b) := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hγ'i : ∀ c d, a ≤ c → c ≤ d → d ≤ b → IntervalIntegrable γ' volume c d := fun c d h1 h2 h3 =>
    (hγ'.mono (Icc_subset_Icc h1 h3)).intervalIntegrable_of_Icc h2
  have hftc : ∀ t ∈ Icc a b, γ t - γ a = ∫ s in a..t, γ' s := by
    intro t ht
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hγ s ?_)
      (hγ'i a t le_rfl ht.1 ht.2)).symm
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  set L := ∫ t in a..b, ‖γ' t‖
  have hnI : ContinuousOn (fun t => ‖γ' t‖) (Icc a b) := hγ'.norm
  have hpos : ∀ t ∈ Icc a b, ‖γ t - γ a‖ ≤ L := by
    intro t ht
    rw [hftc t ht]
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall (fun s => norm_nonneg _)) ?_
    exact hnI.intervalIntegrable_of_Icc hab
  -- remove the base point
  have hsplit : ∫ t in a..b, σ (γ t - q) (γ' t) =
      (∫ t in a..b, σ (γ t - γ a) (γ' t)) + σ (γ a - q) (∫ t in a..b, γ' t) := by
    have hint1 : IntervalIntegrable (fun t => σ (γ t - γ a) (γ' t)) volume a b :=
      (((σ.continuous.comp_continuousOn (hγc.sub continuousOn_const))).clm_apply
        hγ').intervalIntegrable_of_Icc hab
    have hint2 : IntervalIntegrable (fun t => σ (γ a - q) (γ' t)) volume a b :=
      ((σ (γ a - q)).continuous.comp_continuousOn hγ').intervalIntegrable_of_Icc hab
    rw [← (σ (γ a - q)).intervalIntegral_comp_comm (hγ'i a b le_rfl hab le_rfl),
      ← intervalIntegral.integral_add hint1 hint2]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show σ (γ t - q) (γ' t) = σ (γ t - γ a) (γ' t) + σ (γ a - q) (γ' t)
    rw [← ContinuousLinearMap.add_apply, ← map_add]
    congr 2; abel
  have hzero : (∫ t in a..b, γ' t) = 0 := by
    rw [← hftc b ⟨hab, le_rfl⟩, hper, sub_self]
  rw [hsplit, hzero, map_zero, add_zero]
  have hbd : |∫ t in a..b, σ (γ t - γ a) (γ' t)| ≤ ∫ t in a..b, ‖σ‖ * L * ‖γ' t‖ := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hab
      (Eventually.of_forall (fun t ht => ?_)) ((hnI.const_smul (‖σ‖ * L)).intervalIntegrable_of_Icc hab)
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    calc ‖σ (γ t - γ a) (γ' t)‖ ≤ ‖σ‖ * ‖γ t - γ a‖ * ‖γ' t‖ := σ.le_opNorm₂ _ _
      _ ≤ ‖σ‖ * L * ‖γ' t‖ := by gcongr; exact hpos t ht'
  rw [intervalIntegral.integral_const_mul] at hbd
  have hCS := sq_integral_le hnI
  have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg σ
  calc _ ≤ ‖σ‖ * L * L := hbd
    _ = ‖σ‖ * L ^ 2 := by ring
    _ ≤ ‖σ‖ * ((b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2) := mul_le_mul_of_nonneg_left hCS hσ0
    _ = _ := by ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (σ : F →L[ℝ] F →L[ℝ] ℝ) {γ γ' : ℝ → F} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t) (hγ' : ContinuousOn γ' (Icc a b))
    (hper : γ a = γ b) (q : F) :
    |∫ t in a..b, σ (γ t - q) (γ' t)| ≤ ‖σ‖ * (b - a) * ∫ t in a..b, ‖γ' t‖ ^ 2 :=
  abs_integral_bilin_sub_le_of_eq_aux σ hab hγ hγ' hper q
