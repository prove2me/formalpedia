-- Prove2me | solution 1 for CompDesignBFM.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:32:57.673205+00:00
-- url     : https://prove2.me/submissions/bd36cee9-4201-410a-8d86-30397c49113e

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_util
import Definitions.Def_CompDesignBFM_tau
import Definitions.Def_CompDesignBFM_thresholdMech
import Definitions.Def_CompDesignBFM_IsMonotoneRule
import Definitions.Def_CompDesignBFM_IsTruthful
import Definitions.Def_CompDesignBFM_IsIR

open CompDesignBFM

theorem solution {n : ℕ} (A : (Fin n → ℝ) → Finset (Fin n)) (hA : IsMonotoneRule A)
    (hbdd : ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∀ i,
      BddAbove {z : ℝ | 0 ≤ z ∧ i ∈ A (Function.update b i z)}) :
    IsTruthful (thresholdMech A) ∧ IsIR (thresholdMech A) := by
  -- the threshold does not depend on the agent's own bid
  have htau : ∀ (b : Fin n → ℝ) (i : Fin n) (w : ℝ),
      tau A (Function.update b i w) i = tau A b i := by
    intro b i w
    unfold tau
    simp [Function.update_idem]
  have hpay : ∀ (b : Fin n → ℝ) (i : Fin n), i ∈ A b → (thresholdMech A).pay b i = tau A b i := by
    intro b i hi
    simp [thresholdMech, hi]
  have hpay0 : ∀ (b : Fin n → ℝ) (i : Fin n), i ∉ A b → (thresholdMech A).pay b i = 0 := by
    intro b i hi
    simp [thresholdMech, hi]
  have hnn : ∀ (b : Fin n → ℝ) (i : Fin n) (w : ℝ), (∀ j, 0 ≤ b j) → 0 ≤ w →
      ∀ j, 0 ≤ Function.update b i w j := by
    intro b i w hb hw j
    by_cases h : j = i
    · subst h; simpa using hw
    · simpa [Function.update_of_ne h] using hb j
  have hu1 : ∀ (b' : Fin n → ℝ) (i : Fin n) (t : ℝ), i ∈ A b' →
      CompDesignBFM.util (thresholdMech A) i t b' = tau A b' i - t := by
    intro b' i t h
    have h' : i ∈ (thresholdMech A).alloc b' := h
    unfold CompDesignBFM.util
    rw [if_pos h', hpay b' i h]
  have hu0 : ∀ (b' : Fin n → ℝ) (i : Fin n) (t : ℝ), i ∉ A b' →
      CompDesignBFM.util (thresholdMech A) i t b' = 0 := by
    intro b' i t h
    have h' : i ∉ (thresholdMech A).alloc b' := h
    unfold CompDesignBFM.util
    rw [if_neg h', hpay0 b' i h]
  refine ⟨?_, ?_⟩
  · intro i t z b ht hz hb
    have hbddZ := hbdd b hb i
    set Z : Set ℝ := {w : ℝ | 0 ≤ w ∧ i ∈ A (Function.update b i w)} with hZ
    have hτ : ∀ w, tau A (Function.update b i w) i = sSup Z := by
      intro w; rw [htau]; rfl
    by_cases hwz : i ∈ A (Function.update b i z)
    · rw [hu1 _ i t hwz]
      by_cases hwt : i ∈ A (Function.update b i t)
      · rw [hu1 _ i t hwt, hτ, hτ]
      · rw [hu0 _ i t hwt, hτ]
        have hzZ : z ∈ Z := ⟨hz, hwz⟩
        have hle : sSup Z ≤ t := by
          by_contra hlt
          push Not at hlt
          obtain ⟨w, hwZ, htw⟩ := exists_lt_of_lt_csSup ⟨z, hzZ⟩ hlt
          have hmon := hA (Function.update b i w) i t (hnn b i w hb hwZ.1) ht
            (by simpa using htw.le) (by simpa using hwZ.2)
          apply hwt
          simpa [Function.update_idem] using hmon
        linarith
    · rw [hu0 _ i t hwz]
      by_cases hwt : i ∈ A (Function.update b i t)
      · rw [hu1 _ i t hwt, hτ]
        have htZ : t ∈ Z := ⟨ht, hwt⟩
        have := le_csSup hbddZ htZ
        linarith
      · rw [hu0 _ i t hwt]
  · intro b hb i hi
    have hi' : i ∈ A b := hi
    show b i ≤ (thresholdMech A).pay b i
    rw [hpay b i hi']
    unfold tau
    exact le_csSup (hbdd b hb i) ⟨hb i, by simpa using hi'⟩
