-- Prove2me | solution 1 for CompDesignBFM.xos_subadditive_self_bounding
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:29:24.766073+00:00
-- url     : https://prove2.me/submissions/7bdb1138-8f5e-4a66-be90-c157adbb93a6

import Mathlib
import Definitions.Def_CompDesignBFM_IsXOS
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_BudgetClock_Subadditive_Setting

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hx : IsXOS v)
    (hm : IsMonotoneSF v) :
    BudgetClock.Subadditive.IsSubadditive v ∧ IsSelfBounding v := by
  obtain ⟨I, hI⟩ := hx
  -- v ∅ = 0
  have hv0 : v ∅ = 0 := by
    obtain ⟨⟨a, _, ha⟩, _⟩ := hI ∅
    have ha' : ∑ i ∈ (∅ : Finset (Fin n)), a i = v ∅ := ha
    simpa using ha'.symm
  -- a maximising clause for U has nonnegative coefficients on U
  have hmax : ∀ U : Finset (Fin n), ∃ a ∈ I, v U = ∑ i ∈ U, a i ∧
      ∀ i ∈ U, 0 ≤ a i := by
    intro U
    obtain ⟨⟨a, haI, ha⟩, _⟩ := hI U
    have ha' : ∑ i ∈ U, a i = v U := ha
    refine ⟨a, haI, ha'.symm, ?_⟩
    intro i hi
    have hle : ∑ j ∈ U.erase i, a j ≤ v (U.erase i) := (hI (U.erase i)).2 ⟨a, haI, rfl⟩
    have hmono : v (U.erase i) ≤ v U := hm _ _ (Finset.erase_subset i U)
    have hsplit : ∑ j ∈ U, a j = a i + ∑ j ∈ U.erase i, a j :=
      (Finset.add_sum_erase U a hi).symm
    linarith
  have hge : ∀ (U : Finset (Fin n)) (a : Fin n → ℝ), a ∈ I → ∑ i ∈ U, a i ≤ v U :=
    fun U a haI => (hI U).2 ⟨a, haI, rfl⟩
  have hnn : ∀ S, 0 ≤ v S := fun S => hv0 ▸ hm ∅ S (Finset.empty_subset S)
  refine ⟨?_, hnn, hm, ?_⟩
  · intro S T
    obtain ⟨a, haI, hUa, hpos⟩ := hmax (S ∪ T)
    have h1 : ∑ i ∈ S ∪ T, a i + ∑ i ∈ S ∩ T, a i = ∑ i ∈ S, a i + ∑ i ∈ T, a i :=
      Finset.sum_union_inter
    have h2 : 0 ≤ ∑ i ∈ S ∩ T, a i :=
      Finset.sum_nonneg fun i hi => hpos i (Finset.mem_union_left _ (Finset.mem_inter.1 hi).1)
    have := hge S a haI
    have := hge T a haI
    linarith
  · intro S
    obtain ⟨a, haI, hSa, _⟩ := hmax S
    have hterm : ∀ i ∈ S, v S - v (S.erase i) ≤ a i := by
      intro i hi
      have hle : ∑ j ∈ S.erase i, a j ≤ v (S.erase i) := hge _ a haI
      have hsplit : ∑ j ∈ S, a j = a i + ∑ j ∈ S.erase i, a j :=
        (Finset.add_sum_erase S a hi).symm
      linarith
    calc ∑ i ∈ S, (v S - v (S.erase i)) ≤ ∑ i ∈ S, a i := Finset.sum_le_sum hterm
      _ = v S := hSa.symm
