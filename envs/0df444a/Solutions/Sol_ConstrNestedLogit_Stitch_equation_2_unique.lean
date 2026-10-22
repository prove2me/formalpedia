-- Prove2me | solution 1 for ConstrNestedLogit.Stitch.equation_2_unique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:59:42.292653+00:00
-- url     : https://prove2.me/submissions/8f26c2b2-c495-44c7-92ef-84cc8fdfe2b5

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

set_option autoImplicit false

open NestedLogitVariants.LP

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (A : ι → Finset (Finset (Fin n)))
    (hA : ∀ i, (A i).Nonempty)
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1) :
    ∃! z : ℝ, I.v0 * z = ∑ i, (A i).sup' (hA i) (fun S =>
      NestedLogitVariants.LP.nestWeight I i S * (NestedLogitVariants.LP.R I i S - z)) := by
  have hW : ∀ i S, 0 ≤ nestWeight I i S := by
    intro i S
    unfold nestWeight V
    refine Real.rpow_nonneg ?_ _
    rw [hvnp i, zero_add]
    exact Finset.sum_nonneg (fun j _ => (hv i j).le)
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun z => ∑ i, (A i).sup' (hA i)
      (fun S => nestWeight I i S * (R I i S - z)) := ⟨_, rfl⟩
  have hanti : ∀ z z' : ℝ, z ≤ z' → H z' ≤ H z := by
    intro z z' h
    rw [hH]
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sup'_le _ _ (fun S hS => ?_)
    refine le_trans ?_ (Finset.le_sup' (fun S => nestWeight I i S * (R I i S - z)) hS)
    exact mul_le_mul_of_nonneg_left (by linarith) (hW i S)
  have hcont : Continuous H := by
    rw [hH]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact Continuous.finset_sup'_apply (f := fun S z => nestWeight I i S * (R I i S - z)) (hA i)
      (fun S _ => by fun_prop)
  have hmono : ∀ z z' : ℝ, z < z' → I.v0 * z - H z < I.v0 * z' - H z' := by
    intro z z' h
    have := hanti z z' h.le
    nlinarith
  -- upper bound
  obtain ⟨C, hC⟩ : ∃ C, C = ∑ i, ∑ S ∈ A i, |nestWeight I i S * R I i S| := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun S _ => abs_nonneg _))
  have hHup : ∀ z : ℝ, 0 ≤ z → H z ≤ C := by
    intro z hz
    rw [hH, hC]
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sup'_le _ _ (fun S hS => ?_)
    have h1 : nestWeight I i S * (R I i S - z) ≤ nestWeight I i S * R I i S := by
      have := mul_nonneg (hW i S) hz; nlinarith
    refine h1.trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun T => |nestWeight I i T * R I i T|)
      (fun T _ => abs_nonneg _) hS
  obtain ⟨Rm, hRm⟩ : ∃ Rm, Rm = ∑ i, ∑ S ∈ A i, |R I i S| := ⟨_, rfl⟩
  have hRm0 : 0 ≤ Rm := by
    rw [hRm]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun S _ => abs_nonneg _))
  have hHlow : ∀ z : ℝ, z ≤ -(1 + Rm) → 0 ≤ H z := by
    intro z hz
    rw [hH]
    refine Finset.sum_nonneg (fun i _ => ?_)
    obtain ⟨S0, hS0⟩ := hA i
    refine le_trans ?_ (Finset.le_sup' (fun S => nestWeight I i S * (R I i S - z)) hS0)
    have h1 : |R I i S0| ≤ Rm := by
      rw [hRm]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => ∑ S ∈ A j, |R I j S|)
        (fun j _ => Finset.sum_nonneg (fun S _ => abs_nonneg _)) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun T => |R I i T|) (fun T _ => abs_nonneg _) hS0
    have h2 : 0 ≤ R I i S0 - z := by
      have := neg_abs_le (R I i S0)
      linarith
    exact mul_nonneg (hW i S0) h2
  have hab : -(1 + Rm) ≤ C / I.v0 := by
    have : 0 ≤ C / I.v0 := div_nonneg hC0 hv0.le
    linarith
  have hfa : I.v0 * (-(1 + Rm)) - H (-(1 + Rm)) ≤ 0 := by
    have := hHlow _ le_rfl
    nlinarith
  have hfb : 0 ≤ I.v0 * (C / I.v0) - H (C / I.v0) := by
    have h1 := hHup (C / I.v0) (div_nonneg hC0 hv0.le)
    have h2 : I.v0 * (C / I.v0) = C := by field_simp
    linarith
  have hcont' : ContinuousOn (fun z => I.v0 * z - H z) (Set.Icc (-(1 + Rm)) (C / I.v0)) :=
    (by fun_prop : Continuous fun z => I.v0 * z - H z).continuousOn
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc hab hcont' ⟨hfa, hfb⟩
  have hz0 : I.v0 * z = H z := by simp only at hz; linarith
  refine ⟨z, ?_, ?_⟩
  · simpa [hH] using hz0
  · intro z' hz'
    have hz1 : I.v0 * z' = H z' := by simpa [hH] using hz'
    rcases lt_trichotomy z' z with h | h | h
    · have := hmono z' z h; linarith
    · exact h
    · have := hmono z z' h; linarith
