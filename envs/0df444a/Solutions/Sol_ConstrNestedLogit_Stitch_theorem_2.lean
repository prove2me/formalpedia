-- Prove2me | solution 1 for ConstrNestedLogit.Stitch.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:10:32.654796+00:00
-- url     : https://prove2.me/submissions/db646e09-4fc7-438e-8fc4-dafd34140643

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
    (A : ι → Finset (Finset (Fin n)))
    (z : ℝ) (y : ι → ℝ) (S_hat : ι → Finset (Fin n))
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1)
    (hlp : NestedLogitVariants.LP.LP4Optimal I (fun i => (A i : Set (Finset (Fin n)))) z y)
    (hmem : ∀ i, S_hat i ∈ A i)
    (hmax : ∀ i S, S ∈ A i →
      NestedLogitVariants.LP.nestWeight I i S * (NestedLogitVariants.LP.R I i S - z) ≤
      NestedLogitVariants.LP.nestWeight I i (S_hat i) *
        (NestedLogitVariants.LP.R I i (S_hat i) - z)) :
    ∀ S : ι → Finset (Fin n), (∀ i, S i ∈ A i) →
      NestedLogitVariants.LP.revenue I S ≤ NestedLogitVariants.LP.revenue I S_hat := by
  have hW : ∀ i S, 0 ≤ nestWeight I i S := by
    intro i S
    unfold nestWeight V
    refine Real.rpow_nonneg ?_ _
    rw [hvnp i, zero_add]
    exact Finset.sum_nonneg (fun j _ => (hv i j).le)
  obtain ⟨hf1, hf2⟩ := hlp.1
  obtain ⟨gh, hgh⟩ : ∃ gh : ι → ℝ, gh = fun i => nestWeight I i (S_hat i) * (R I i (S_hat i) - z) :=
    ⟨_, rfl⟩
  have hge : ∑ i, gh i ≤ I.v0 * z := by
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hf1
    rw [hgh]
    exact hf2 i (S_hat i) (Finset.mem_coe.2 (hmem i))
  have hle : I.v0 * z ≤ ∑ i, gh i := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨M, hM⟩ : ∃ M : ι → ℝ, M = fun i => ∑ T ∈ A i, nestWeight I i T := ⟨_, rfl⟩
    have hM0 : ∀ i, 0 ≤ M i := fun i => by
      rw [hM]; exact Finset.sum_nonneg (fun T _ => hW i T)
    have hMS : ∀ i S, S ∈ A i → nestWeight I i S ≤ M i := fun i S hS => by
      rw [hM]; exact Finset.single_le_sum (f := fun T => nestWeight I i T) (fun T _ => hW i T) hS
    obtain ⟨Mt, hMt⟩ : ∃ Mt, Mt = ∑ i, M i := ⟨_, rfl⟩
    have hMt0 : 0 ≤ Mt := by rw [hMt]; exact Finset.sum_nonneg (fun i _ => hM0 i)
    obtain ⟨g, hg⟩ : ∃ g, g = I.v0 * z - ∑ i, gh i := ⟨_, rfl⟩
    have hgpos : 0 < g := by rw [hg]; linarith
    obtain ⟨ε, hε⟩ : ∃ ε, ε = g / (2 * (Mt + I.v0 + 1)) := ⟨_, rfl⟩
    have hεpos : 0 < ε := by rw [hε]; exact div_pos hgpos (by linarith)
    have hε2 : ε * (2 * (Mt + I.v0 + 1)) = g := by rw [hε]; field_simp
    have hfeas : LP4Feasible I (fun i => (A i : Set (Finset (Fin n)))) (z - ε)
        (fun i => gh i + ε * M i) := by
      refine ⟨?_, fun i S hS => ?_⟩
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hMt]
        nlinarith
      · have hS' : S ∈ A i := Finset.mem_coe.1 hS
        have h1 := hmax i S hS'
        have h2 : ε * nestWeight I i S ≤ ε * M i :=
          mul_le_mul_of_nonneg_left (hMS i S hS') hεpos.le
        have h3 : nestWeight I i S * (R I i S - (z - ε)) =
            nestWeight I i S * (R I i S - z) + ε * nestWeight I i S := by ring
        have hgi : gh i = nestWeight I i (S_hat i) * (R I i (S_hat i) - z) := by rw [hgh]
        show nestWeight I i S * (R I i S - (z - ε)) ≤ gh i + ε * M i
        rw [h3]
        linarith
    have := hlp.2 _ _ hfeas
    linarith
  have heq : I.v0 * z = ∑ i, gh i := le_antisymm hle hge
  intro T hT
  have hz : z = revenue I S_hat := (cns_rev_char I S_hat z hvnp hv0 hv).1.1 (by rw [heq, hgh])
  have hT' : I.v0 * z ≥ ∑ i, nestWeight I i (T i) * (R I i (T i) - z) := by
    rw [heq, hgh]
    exact Finset.sum_le_sum (fun i _ => hmax i (T i) (hT i))
  have := (cns_rev_char I T z hvnp hv0 hv).2.1 hT'
  rw [← hz]
  exact this
