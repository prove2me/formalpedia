-- Prove2me | solution 1 for FinNetProp.Mitosis.part_II
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T16:15:14.971297+00:00
-- url     : https://prove2.me/submissions/41bc7889-1534-4cf4-b5cb-4903b327a2ef

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting
import Theorems.Thm_FinNetProp_Mitosis_part_II_rational
import Theorems.Thm_FinNetProp_Mitosis_part_I_limit_solution

namespace FinNetProp.Mitosis

open Finset Filter Topology

/-- Rational approximation from below. -/
noncomputable def fnpQ_approx (x : ℝ) (n : ℕ) : ℝ := (⌊x * ((n : ℝ) + 1)⌋ : ℝ) / ((n : ℝ) + 1)

lemma fnpQ_approx_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ fnpQ_approx x n := by
  unfold fnpQ_approx
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.2 (mul_nonneg hx (by positivity))

lemma fnpQ_approx_zero (n : ℕ) : fnpQ_approx 0 n = 0 := by simp [fnpQ_approx]

lemma fnpQ_approx_rat (x : ℝ) (n : ℕ) : ∃ q : ℚ, fnpQ_approx x n = q :=
  ⟨(⌊x * ((n : ℝ) + 1)⌋ : ℚ) / ((n : ℚ) + 1), by unfold fnpQ_approx; push_cast; rfl⟩

lemma fnpQ_approx_tendsto (x : ℝ) : Tendsto (fun n => fnpQ_approx x n) atTop (𝓝 x) := by
  have hlow : ∀ n : ℕ, x - 1 / ((n : ℝ) + 1) ≤ fnpQ_approx x n := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    unfold fnpQ_approx
    rw [le_div_iff₀ hpos]
    have := Int.lt_floor_add_one (x * ((n : ℝ) + 1))
    have e : (x - 1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = x * ((n : ℝ) + 1) - 1 := by
      field_simp
    rw [e]; linarith
  have hup : ∀ n : ℕ, fnpQ_approx x n ≤ x := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    unfold fnpQ_approx
    rw [div_le_iff₀ hpos]
    exact Int.floor_le _
  have h0 : Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_sub x
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds hlow hup

/-- The rational approximating network `F^n`. -/
noncomputable def fnpQ_net (F : FinNet) (n : ℕ) : FinNet where
  N := F.N
  N_nonempty := F.N_nonempty
  z := F.z
  L := fun i j => fnpQ_approx (F.L i j) n
  z_pos := F.z_pos
  L_nonneg := fun i j => fnpQ_approx_nonneg _ (F.L_nonneg i j) n
  L_diag := fun i => by rw [F.L_diag i, fnpQ_approx_zero]
  z_out := F.z_out
  L_out := fun i j h => by rw [F.L_out i j h, fnpQ_approx_zero]

theorem fnp_part_II (b : BankruptcyRule) (hcb : ClaimsBounded b) (hll : LimitedLiability b)
    (hpc : PriorityOfCreditors b) (hcont : RuleContinuous b) (himp : Impartial b)
    (hmit : InvariantToMitosis b) :
    ∀ F : FinNet, IsPropSolution F (b F) := by
  intro F
  have hconv : NetConverges (fnpQ_net F) F :=
    ⟨Filter.Eventually.of_forall (fun n => rfl), fun i => tendsto_const_nhds,
      fun i j => fnpQ_approx_tendsto (F.L i j)⟩
  have hrat : ∀ n, IsPropSolution (fnpQ_net F n) (b (fnpQ_net F n)) := by
    intro n
    exact part_II_rational b hcb hll hpc himp hmit (fnpQ_net F n)
      (fun i j => fnpQ_approx_rat (F.L i j) n)
  exact part_I_limit_solution (fnpQ_net F) F hconv (fun n => b (fnpQ_net F n)) hrat (b F)
    (hcont (fnpQ_net F) F hconv)

end FinNetProp.Mitosis

theorem solution (b : FinNetProp.Mitosis.BankruptcyRule) (hcb : FinNetProp.Mitosis.ClaimsBounded b)
    (hll : FinNetProp.Mitosis.LimitedLiability b)
    (hpc : FinNetProp.Mitosis.PriorityOfCreditors b) (hcont : FinNetProp.Mitosis.RuleContinuous b)
    (himp : FinNetProp.Mitosis.Impartial b)
    (hmit : FinNetProp.Mitosis.InvariantToMitosis b) :
    ∀ F : FinNetProp.Mitosis.FinNet, FinNetProp.Mitosis.IsPropSolution F (b F) :=
  FinNetProp.Mitosis.fnp_part_II b hcb hll hpc hcont himp hmit
