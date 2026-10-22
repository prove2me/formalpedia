-- Prove2me | solution 1 for ConstrNestedLogit.Stitch.revenue_characterization
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:57:35.677984+00:00
-- url     : https://prove2.me/submissions/48204fee-b52e-46df-aa3c-eb97787317af

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

set_option autoImplicit false

open NestedLogitVariants.LP

lemma cns_rev_char {ι : Type*} [Fintype ι] {n : ℕ}
    (I : Instance ι n) (S : ι → Finset (Fin n)) (z : ℝ)
    (hvnp : ∀ i, I.vnp i = 0) (hv0 : 0 < I.v0) (hv : ∀ i j, 0 < I.v i j) :
    (I.v0 * z = ∑ i, nestWeight I i (S i) * (R I i (S i) - z) ↔ z = revenue I S) ∧
    (I.v0 * z ≥ ∑ i, nestWeight I i (S i) * (R I i (S i) - z) ↔ revenue I S ≤ z) := by
  have hW : ∀ i, 0 ≤ nestWeight I i (S i) := by
    intro i
    unfold nestWeight V
    refine Real.rpow_nonneg ?_ _
    rw [hvnp i, zero_add]
    exact Finset.sum_nonneg (fun j _ => (hv i j).le)
  have hD : 0 < I.v0 + ∑ i, nestWeight I i (S i) :=
    add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg (fun i _ => hW i))
  have hexp : ∑ i, nestWeight I i (S i) * (R I i (S i) - z) =
      ∑ i, nestWeight I i (S i) * R I i (S i) - z * ∑ i, nestWeight I i (S i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold revenue
  rw [hexp]
  constructor
  · rw [eq_div_iff hD.ne']
    constructor <;> intro h <;> linarith
  · rw [div_le_iff₀ hD]
    constructor <;> intro h <;> linarith

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (S : ι → Finset (Fin n)) (z : ℝ)
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1) :
    (I.v0 * z = ∑ i, NestedLogitVariants.LP.nestWeight I i (S i) *
      (NestedLogitVariants.LP.R I i (S i) - z) ↔
      z = NestedLogitVariants.LP.revenue I S) ∧
    (I.v0 * z ≥ ∑ i, NestedLogitVariants.LP.nestWeight I i (S i) *
      (NestedLogitVariants.LP.R I i (S i) - z) ↔
      NestedLogitVariants.LP.revenue I S ≤ z) :=
  cns_rev_char I S z hvnp hv0 hv
