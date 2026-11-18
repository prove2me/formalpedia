-- Prove2me | solution 1 for CompDesign.eq_22_23
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:25:10.482864+00:00
-- url     : https://prove2.me/submissions/a8465ca0-70b4-4393-9031-b862cde000a5

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (hS : IsPNE v B c S) (hpos : 0 < v S)
    (i : Fin n) (hi : i ∉ S) :
    (v (insert i S) ≤ v S * (B / (B - c i)) ∧ v (insert i S) - v S ≤ v S * (c i / (B - c i))) ∧
    v (insert i S) - v S ≤ (c i / B) / (1 - c i / B) * v S := by
  have hmono : v S ≤ v (insert i S) := hm S _ (Finset.subset_insert i S)
  have hpos' : 0 < v (insert i S) := lt_of_lt_of_le hpos hmono
  have hne : 0 < B - c i := by linarith [hcB i]
  have hpne := hS.2 i hi
  have hmc : mcPay v B (insert i S) i = B * (v (insert i S) - v S) / v (insert i S) := by
    simp [mcPay, hpos', Finset.erase_insert hi]
  rw [hmc, div_le_iff₀ hpos'] at hpne
  -- hpne : B * (a - s) ≤ c * a
  have key : v (insert i S) * (B - c i) ≤ B * v S := by nlinarith
  have h1 : v (insert i S) ≤ v S * (B / (B - c i)) := by
    rw [mul_div_assoc', le_div_iff₀ hne]; linarith
  have h2 : v (insert i S) - v S ≤ v S * (c i / (B - c i)) := by
    have : v S * (B / (B - c i)) - v S = v S * (c i / (B - c i)) := by
      field_simp; ring
    linarith
  refine ⟨⟨h1, h2⟩, ?_⟩
  have e : (c i / B) / (1 - c i / B) = c i / (B - c i) := by
    have hB0 : B ≠ 0 := hB.ne'
    have hne0 : B - c i ≠ 0 := hne.ne'
    field_simp
  rw [e, mul_comm]
  exact h2.trans (le_of_eq (by ring))
