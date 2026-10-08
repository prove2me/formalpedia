-- Prove2me | solution 1 for CHMSPricing.UnitDemand.truthful_weaklyMonotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:08:45.565801+00:00
-- url     : https://prove2.me/submissions/afce08d2-082d-4f3f-b775-168e9c2eab09

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism



namespace CHMSPricing.UnitDemand

theorem twm_core {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (A : MultiMechanism J m)
    (hA : IsTruthfulMulti D 𝒥 owner A) :
    WeaklyMonotone D owner A := by
  intro i v₁ h₁ v₂ h₂ hag
  have a := hA.dsic v₁ h₁ i v₂ h₂ (fun j hj => (hag j hj).symm)
  have b := hA.dsic v₂ h₂ i v₁ h₁ (fun j hj => hag j hj)
  unfold MultiMechanism.utility at a b
  linarith

theorem cam_core {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (A : MultiMechanism J m) (hA : IsTruthfulMulti D 𝒥 owner A)
    (v : J → ℝ) (hv : v ∈ typeSpace D) (j : J) (x y : ℝ)
    (hx : x ∈ Set.Icc (D j).lo (D j).hi) (hy : y ∈ Set.Icc (D j).lo (D j).hi) (hxy : x ≤ y)
    (hj : j ∈ A.alloc (Function.update v j x)) :
    j ∈ A.alloc (Function.update v j y) := by
  by_contra hn
  set i := owner j
  have mem : ∀ z ∈ Set.Icc (D j).lo (D j).hi, Function.update v j z ∈ typeSpace D := by
    intro z hz k _
    by_cases hk : k = j
    · subst hk; simpa using hz
    · simpa [Function.update_of_ne hk] using hv k (Set.mem_univ _)
  have h1 := mem x hx
  have h2 := mem y hy
  have W := twm_core D 𝒥 owner A hA i _ h1 _ h2 (by
    intro k hk
    have : k ≠ j := fun h => hk (h ▸ rfl)
    simp [Function.update_of_ne this])
  unfold MultiMechanism.valueOf at W
  have F1 : (A.alloc (Function.update v j x)).filter (fun k => owner k = i) = {j} := by
    have hc := h𝒥 _ (hA.feasible _ h1) i
    have hjm : j ∈ (A.alloc (Function.update v j x)).filter (fun k => owner k = i) :=
      Finset.mem_filter.2 ⟨hj, rfl⟩
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.2 hjm)
    intro k hk
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.1 hc k hk j hjm
  rw [F1] at W
  have S : ∑ k ∈ (A.alloc (Function.update v j y)).filter (fun k => owner k = i),
      Function.update v j x k =
      ∑ k ∈ (A.alloc (Function.update v j y)).filter (fun k => owner k = i),
      Function.update v j y k := by
    apply Finset.sum_congr rfl
    intro k hk
    have : k ≠ j := by
      rintro rfl; exact hn (Finset.mem_filter.1 hk).1
    simp [Function.update_of_ne this]
  rw [S] at W
  simp at W
  have hxy' : x = y := le_antisymm hxy (by linarith)
  exact hn (hxy' ▸ hj)

end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m) (A : MultiMechanism J m)
    (hA : IsTruthfulMulti D 𝒥 owner A) :
    WeaklyMonotone D owner A := by
  exact twm_core D 𝒥 owner A hA
