-- Prove2me | solution 1 for Formalism.HF.apLogDensity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:06.557566+00:00
-- url     : https://prove2.me/submissions/55c1956e-5a15-44b8-98b1-ec3679e854a5

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Theorems.Thm_Formalism_HF_P_apld_tsum_residueClass_eq
import Theorems.Thm_Formalism_HF_P_apld_summable
import Theorems.Thm_Formalism_HF_P_residue_class_l_function_tendsto
import Theorems.Thm_Formalism_HF_P_apld_nonprime_nonneg
import Theorems.Thm_Formalism_HF_P_apld_nonprime_le
import Theorems.Thm_Formalism_HF_P_apld_prime_part_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism.HF.P
namespace Formalism.HF
theorem _root_.solution : Formalism.HF.APLogDensity := by
  intro N _ a ha
  unfold Formalism.HF.LogDensity
  set P : ℝ → ℕ → ℝ := fun x n => (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x with hP
  set Q : ℝ → ℕ → ℝ := fun x n => (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x with hQ
  have hPQ : ∀ x n, residueClass a n / (n : ℝ) ^ x = P x n + Q x n := by
    intro x n
    simp only [hP, hQ, ← add_div]
    congr 1
    split_ifs <;> simp
  have hPnn : ∀ x n, 0 ≤ P x n := by
    intro x n
    simp only [hP]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) x)
    split_ifs
    · exact residueClass_nonneg a n
    · exact le_rfl
  have hQnn : ∀ x n, 0 ≤ Q x n := fun x n => apld_nonprime_nonneg a x n
  have hPs : ∀ x : ℝ, 1 < x → Summable (P x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hPnn x) (fun n => by rw [hPQ]; linarith [hQnn x n])
  have hQs : ∀ x : ℝ, 1 < x → Summable (Q x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hQnn x) (fun n => by rw [hPQ]; linarith [hPnn x n])
  have hB : Summable fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n :=
    summable_residueClass_non_primes_div a
  set B := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n with hBdef
  have hQle : ∀ x : ℝ, 1 < x → ∑' n, Q x n ≤ B := fun x hx =>
    (hQs x hx).tsum_le_tsum (fun n => apld_nonprime_le a hx.le n) hB
  have hsplit : ∀ x : ℝ, 1 < x →
      (x - 1) * (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ - (x - 1) * ∑' n, Q x n =
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) := by
    intro x hx
    have hsum : ∑' n, residueClass a n / (n : ℝ) ^ x = ∑' n, P x n + ∑' n, Q x n := by
      rw [← (hPs x hx).tsum_add (hQs x hx)]
      exact tsum_congr (hPQ x)
    have hPind : ∑' n, P x n = ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n :=
      tsum_congr (fun n => apld_prime_part_eq a x n)
    have hT := apld_tsum_residueClass_eq ha hx
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 hx.ne'
    rw [← hPind]
    have : ∑' n, P x n = (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ / (x - 1) - ∑' n, Q x n := by
      linarith
    rw [this]
    field_simp
  have h1 : Tendsto (fun x : ℝ => (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) :=
    residue_class_l_function_tendsto a
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun x : ℝ => (x - 1) * ∑' n, Q x n) (𝓝[>] 1) (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => (x - 1) * B) (𝓝[>] 1) (𝓝 0) := by
      simpa using hlin.mul_const B
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg (sub_nonneg.2 (le_of_lt hx)) (tsum_nonneg (hQnn x))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_le_mul_of_nonneg_left (hQle x hx) (sub_nonneg.2 (le_of_lt hx))
  have hlim := (h1.add (tendsto_const_nhds (x := (N.totient : ℝ)⁻¹))).sub h3
  have e : (0 : ℝ) + (N.totient : ℝ)⁻¹ - 0 = 1 / (N.totient : ℝ) := by simp
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hsplit x hx
end Formalism.HF
