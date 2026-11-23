-- Prove2me | solution 1 for Experiments.exists_eq_exp_of_semigroup_nonstandard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:50.795319+00:00
-- url     : https://prove2.me/submissions/820d99ba-2ea3-4749-9cc1-9aad06daba5f

import Mathlib
import Definitions.Def_Experiments_NonstandardSemigroup
import Theorems.Thm_Experiments_eq_of_infinitesimal_steps

set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A]
variable [CompleteSpace A]
namespace Experiments
theorem _root_.solution [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  -- The positive infinitesimal `ε = 1 / ω`, as a sequence along `hyperfilter ℕ`, the scale
  -- `η`, and the change `q` on that scale.
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let η : ℕ → ℝ := fun n => ε n + ‖M (ε n) - 1‖
  let q : ℕ → A := fun n => (η n)⁻¹ • (M (ε n) - 1)
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  have hεη : ∀ n, ε n ≤ η n := fun n => le_add_of_nonneg_right (norm_nonneg _)
  have hη : ∀ n, 0 < η n := fun n => (hε n).trans_le (hεη n)
  have hεz : Tendsto ε (hyperfilter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left Nat.hyperfilter_le_atTop
  have hηz : Tendsto η (hyperfilter ℕ) (𝓝 0) := by
    have hM : Tendsto (fun n => M (ε n)) (hyperfilter ℕ) (𝓝 1) := by
      simpa [h0, Function.comp_def] using (hcont 0 (by simp)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hεz, Eventually.of_forall fun n => (hε n).le⟩)
    simpa using hεz.add (hM.sub_const 1).norm
  have hsum : ∀ n, ε n / η n = 1 - ‖q n‖ := fun n => by
    have := (hη n).ne'
    simp only [q, norm_smul, norm_inv, Real.norm_of_nonneg (hη n).le]
    field_simp
    simp only [η]
    ring
  -- The standard part `B` of `q`, and `ε / η ≈ a = 1 - ‖B‖`.
  obtain ⟨B, hB1, hB : Tendsto q (hyperfilter ℕ) (𝓝 B)⟩ :=
    (isCompact_closedBall (0 : A) 1).ultrafilter_le_nhds (.map q (hyperfilter ℕ)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact mem_map.mpr (univ_mem' fun n => by
        simpa using (show ‖q n‖ ≤ 1 by
          linarith [hsum n, div_nonneg (hε n).le (hη n).le])))
  let a : ℝ := 1 - ‖B‖
  have ha : Tendsto (fun n => ε n / η n) (hyperfilter ℕ) (𝓝 a) :=
    (tendsto_const_nhds.sub hB.norm).congr fun n => (hsum n).symm
  -- The exponential `E u = exp (u B)` takes the same step on that scale, to first order.
  let E : ℝ → A := fun u => exp (u • B)
  have hE : Continuous E := continuous_iff_continuousAt.mpr fun u =>
    (hasDerivAt_exp_smul_const B u).continuousAt
  have hEadd : ∀ u v, E (u + v) = E u * E v := fun u v => by
    simp only [E, add_smul]
    exact exp_add_of_commute (((Commute.refl B).smul_left u).smul_right v)
  have hEd : Tendsto (fun n => (η n)⁻¹ • (E (η n) - 1)) (hyperfilter ℕ) (𝓝 B) := by
    simpa [E, Function.comp_def] using
      (hasDerivAt_exp_smul_const' B 0).tendsto_slope_zero_right.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hηz, Eventually.of_forall hη⟩)
  have hstep : Tendsto (fun n => (η n)⁻¹ • (M (ε n) - E (η n))) (hyperfilter ℕ) (𝓝 0) := by
    simpa using (hB.sub hEd).congr fun n => by
      simp only [q, smul_sub]
      abel
  -- Euler's step, and the semigroup is not infinitely fast.
  have hmain : ∀ s, 0 ≤ s → M (s * a) = E s := fun s hs =>
    eq_of_infinitesimal_steps M E hcont h0 hadd hE.continuousOn (by simp [E])
      (fun u v _ _ => hEadd u v) ε η (fun n => (hε n).le) hεη hη hηz ha hstep hs
  have ha0 : a ≠ 0 := fun h => by
    have hB0 : B = 0 := tendsto_nhds_unique hEd (tendsto_const_nhds.congr fun n => by
      rw [← hmain _ (hη n).le, h, mul_zero, h0, sub_self, smul_zero])
    simp [a, hB0] at h
  have hapos : 0 < a :=
    lt_of_le_of_ne (sub_nonneg.mpr (mem_closedBall_zero_iff.mp hB1)) (Ne.symm ha0)
  refine ⟨a⁻¹ • B, fun t ht => ?_⟩
  have h := hmain (t / a) (div_nonneg ht hapos.le)
  rw [div_mul_cancel₀ t ha0] at h
  rw [h, smul_smul, div_eq_mul_inv]
end Experiments
