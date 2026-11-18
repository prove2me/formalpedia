-- Prove2me | solution 1 for CompDesign.thm_5_1_zero_case
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:26:18.023645+00:00
-- url     : https://prove2.me/submissions/6c6e4e88-4087-40f6-9f0c-c6d276bf4317

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (hS : IsPNE v B c S) (hzero : v S = 0) :
    OPT v B c = 0 := by
  have hnn : ∀ T, 0 ≤ v T := fun T => hv0 ▸ hm ∅ T (Finset.empty_subset T)
  have hmarg : ∀ i, i ∉ S → v (insert i S) = 0 := by
    intro i hi
    have hge : v S ≤ v (insert i S) := hm S _ (Finset.subset_insert i S)
    by_contra hne
    have hpos : 0 < v (insert i S) := lt_of_le_of_ne (hnn _) (Ne.symm hne)
    have hpne := hS.2 i hi
    have hmc : mcPay v B (insert i S) i = B := by
      simp [mcPay, hpos, Finset.erase_insert hi, hzero]
      field_simp
    rw [hmc] at hpne
    linarith [hcB i]
  have hU : ∀ U : Finset (Fin n), v (S ∪ U) = 0 := by
    intro U
    induction U using Finset.induction_on with
    | empty => simpa using hzero
    | insert j U hj ih =>
      by_cases hjS : j ∈ S ∪ U
      · have : S ∪ insert j U = S ∪ U := by
          rw [Finset.union_insert]; exact Finset.insert_eq_of_mem hjS
        rw [this]; exact ih
      · have hjS' : j ∉ S := fun h => hjS (Finset.mem_union_left _ h)
        have hsub := hs S (S ∪ U) j Finset.subset_union_left hjS
        rw [hmarg j hjS', hzero, ih] at hsub
        have : S ∪ insert j U = insert j (S ∪ U) := Finset.union_insert j S U
        rw [this]
        linarith [hnn (insert j (S ∪ U))]
  have hall : ∀ T, v T = 0 := by
    intro T
    have h1 : v T ≤ v (S ∪ T) := hm T _ Finset.subset_union_right
    linarith [hnn T, hU T]
  obtain ⟨T, _, hT⟩ := (OPT_isGreatest v hB.le c).1
  rw [← hT]; exact hall T
