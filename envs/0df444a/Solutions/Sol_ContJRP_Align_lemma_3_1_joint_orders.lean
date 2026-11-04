-- Prove2me | solution 1 for ContJRP.Align.lemma_3_1_joint_orders
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:09:37.855195+00:00
-- url     : https://prove2.me/submissions/79578690-024f-48a0-afd9-d6d3d14540bc

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active
import Theorems.Thm_ContJRP_Align_lemma_3_2_crossing
import Theorems.Thm_ContJRP_Align_lemma_3_3_uncrossing

open ContJRP.Align
open Classical

theorem jrp31_mem_inf {ι : Type*} (N : Finset ι) (hN : N.Nonempty) (S : ι → Finset ℝ) (x : ℝ) :
    x ∈ N.inf' hN S ↔ ∀ i ∈ N, x ∈ S i := by
  rw [← Finset.singleton_subset_iff, Finset.le_inf'_iff]
  simp

/-- Inclusion–exclusion split into uncrossing and crossing sets: `N(R, Δ) = (I) + (II)`. -/
theorem jrp31_split {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar R : ℕ → ℝ) (Δ : ℝ) :
    ((numOrders (active ε Tt Tstar) R Δ : ℕ) : ℤ) =
      termI ε Tt Tstar Rstar R Δ + termII ε Tt Tstar Rstar R Δ := by
  set A := active ε Tt Tstar
  set S : ℕ → Finset ℝ := fun ℓ => multiplesUpTo (R ℓ) Δ
  have hie := Finset.inclusion_exclusion_card_biUnion A S
  set f : Finset ℕ → ℤ := fun B => (-1 : ℤ) ^ (B.card + 1) * ((interMultiples B R Δ).card : ℤ)
  set P := A.powerset.filter (fun B => B.Nonempty) with hP
  have h1 : ((A.biUnion S).card : ℤ) = ∑ B ∈ P, f B := by
    rw [hie, ← Finset.sum_coe_sort P]
    apply Finset.sum_congr rfl
    intro t _
    have ht := Finset.mem_filter.1 t.2
    simp only [f]
    congr 3
    ext x
    rw [jrp31_mem_inf]
    unfold interMultiples
    rw [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro h
      obtain ⟨ℓ, hℓ⟩ := ht.2
      exact ⟨⟨ℓ, hℓ, h ℓ hℓ⟩, h⟩
    · intro h; exact h.2
  unfold numOrders
  rw [h1, ← Finset.sum_filter_add_sum_filter_not P (fun B => IsUncrossing ε Tt Tstar Rstar B)]
  unfold termI termII
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    rw [hP, Finset.filter_filter]
    apply Finset.filter_congr
    intro B _
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    rw [hP, Finset.filter_filter]

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar)
    (R : ℕ → ℝ) (hfeas : IsLPFeasible ε Tt Tstar Rstar R)
    (hmis : CrossMisaligned ε Tt Tstar Rstar R) :
    ∀ Δ : ℝ, 0 ≤ Δ → (numOrders (active ε Tt Tstar) R Δ : ℝ) ≤
      (1 + 5 * ε) * (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) +
        5 * ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card := by
  intro Δ hΔ
  have hsplit := jrp31_split ε Tt Tstar Rstar R Δ
  have hI := lemma_3_3_uncrossing ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR R hfeas Δ hΔ
  have hII := lemma_3_2_crossing ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2 Rstar hR R hfeas hmis Δ hΔ
  have h0 := observation_2_3_first_segment_active ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2
  have hcard : (1 : ℝ) ≤ ((active ε Tt Tstar).card : ℝ) := by
    have : 1 ≤ (active ε Tt Tstar).card := Finset.card_pos.mpr ⟨0, h0⟩
    exact_mod_cast this
  have hpow : (0 : ℝ) < 2 ^ (active ε Tt Tstar).card := by positivity
  have hsq : (1 : ℝ) ≤ ((active ε Tt Tstar).card : ℝ) ^ 2 := by nlinarith
  have h2 : (2 : ℝ) ^ (active ε Tt Tstar).card ≤
      ((active ε Tt Tstar).card : ℝ) ^ 2 * 2 ^ (active ε Tt Tstar).card := by nlinarith
  have hcast : (numOrders (active ε Tt Tstar) R Δ : ℝ) =
      ((termI ε Tt Tstar Rstar R Δ : ℤ) : ℝ) + ((termII ε Tt Tstar Rstar R Δ : ℤ) : ℝ) := by
    have := congrArg (Int.cast (R := ℝ)) hsplit
    push_cast at this
    exact this
  rw [hcast]
  have hN : (0 : ℝ) ≤ (numOrders (active ε Tt Tstar) Rstar Δ : ℝ) := Nat.cast_nonneg _
  nlinarith
