-- Prove2me | solution 1 for CompDesignBFM.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:47:54.3107+00:00
-- url     : https://prove2.me/submissions/2d575734-2134-4cb2-89bc-71e53370bf1b

import Mathlib
import Definitions.Def_CompDesignBFM_closure
import Definitions.Def_CompDesignBFM_OPT

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hv : ∀ S, 0 ≤ v S) (B : ℝ)
    (hB : 0 < B) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    OPT (closure v) B c = OPT v B c := by
  apply le_antisymm
  · obtain ⟨T0, hT0, hval⟩ := (OPT_isGreatest (closure v) hB.le c).1
    have hT0' : ∑ i ∈ T0, c i ≤ B := hT0
    have hcl : closure v T0 = OPT (closure v) B c := hval
    obtain ⟨T', hT'mem, hT'eq⟩ := Finset.exists_mem_eq_sup'
      (⟨∅, Finset.empty_mem_powerset T0⟩ : T0.powerset.Nonempty) v
    have hsub : T' ⊆ T0 := Finset.mem_powerset.1 hT'mem
    have hfeas : ∑ i ∈ T', c i ≤ B :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hc i)) hT0'
    have h1 : v T' ≤ OPT v B c := (OPT_isGreatest v hB.le c).2 ⟨T', hfeas, rfl⟩
    have : closure v T0 = v T' := by
      unfold CompDesignBFM.closure; exact hT'eq
    rw [← hcl, this]; exact h1
  · obtain ⟨T, hT, hval⟩ := (OPT_isGreatest v hB.le c).1
    have hT' : ∑ i ∈ T, c i ≤ B := hT
    have hle : v T ≤ closure v T := by
      unfold CompDesignBFM.closure
      exact Finset.le_sup' v (Finset.mem_powerset_self T)
    have h2 : closure v T ≤ OPT (closure v) B c :=
      (OPT_isGreatest (closure v) hB.le c).2 ⟨T, hT', rfl⟩
    have hv' : v T = OPT v B c := hval
    linarith
