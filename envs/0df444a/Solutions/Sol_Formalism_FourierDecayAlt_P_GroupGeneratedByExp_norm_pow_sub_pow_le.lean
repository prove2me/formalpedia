-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:08:45.141052+00:00
-- url     : https://prove2.me/submissions/315d5a72-0297-474b-94eb-3703a78080da

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Polynomial difference bound: if `a` and `b` are both `q`-contractive, then
`‖a ^ m - b ^ m‖ ≤ m * q ^ m * ‖a - b‖`. -/
theorem solution {a b : 𝔸} {q : ℝ} (hq : 1 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖)
    (hb : ∀ u, ‖b * u‖ ≤ q * ‖u‖) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
  have hpow : ∀ (c : 𝔸), (∀ u, ‖c * u‖ ≤ q * ‖u‖) → ∀ (n : ℕ) (u : 𝔸), ‖c ^ n * u‖ ≤ q ^ n * ‖u‖ := by
    intro c hc n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      calc ‖c ^ (n + 1) * u‖ = ‖c ^ n * (c * u)‖ := by rw [pow_succ, mul_assoc]
        _ ≤ q ^ n * ‖c * u‖ := ih (c * u)
        _ ≤ q ^ n * (q * ‖u‖) := mul_le_mul_of_nonneg_left (hc u) (by positivity)
        _ = q ^ (n + 1) * ‖u‖ := by rw [pow_succ]; ring
  have hb1 : ∀ n : ℕ, ‖b ^ n‖ ≤ q ^ n * ‖(1 : 𝔸)‖ := by
    intro n
    simpa using hpow b hb n 1
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    rw [hsplit]
    set A : ℝ := ‖a - b‖ * ‖(1 : 𝔸)‖ with hAdef
    have hA : 0 ≤ A := by rw [hAdef]; positivity
    have hq0 : (0:ℝ) ≤ q := by linarith
    have hqpow : q ^ m ≤ q ^ (m + 1) := by
      rw [pow_succ]
      simpa using mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ q ^ m)
    have step2 : q * ‖a ^ m - b ^ m‖ ≤ q * ((m : ℝ) * q ^ m * A) :=
      mul_le_mul_of_nonneg_left ih hq0
    have step3 : ‖a - b‖ * ‖b ^ m‖ ≤ ‖a - b‖ * (q ^ m * ‖(1 : 𝔸)‖) :=
      mul_le_mul_of_nonneg_left (hb1 m) (norm_nonneg _)
    have key : ‖a - b‖ * (q ^ m * ‖(1 : 𝔸)‖) = q ^ m * A := by
      rw [hAdef]; ring
    calc ‖a * (a ^ m - b ^ m) + (a - b) * b ^ m‖
        ≤ ‖a * (a ^ m - b ^ m)‖ + ‖(a - b) * b ^ m‖ := norm_add_le _ _
      _ ≤ q * ‖a ^ m - b ^ m‖ + ‖a - b‖ * ‖b ^ m‖ :=
            add_le_add (ha _) (norm_mul_le _ _)
      _ ≤ q * ((m : ℝ) * q ^ m * A) + ‖a - b‖ * (q ^ m * ‖(1 : 𝔸)‖) :=
            add_le_add step2 step3
      _ = ((m : ℝ) * q ^ (m + 1) + q ^ m) * A := by
            rw [key, pow_succ]; ring
      _ ≤ (((m : ℝ) + 1) * q ^ (m + 1)) * A := by
            have hqq : q ^ m * A ≤ q ^ (m + 1) * A :=
              mul_le_mul_of_nonneg_right hqpow hA
            nlinarith [hqq]
      _ = ((m + 1 : ℕ) : ℝ) * q ^ (m + 1) * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
            rw [hAdef]; push_cast; ring
