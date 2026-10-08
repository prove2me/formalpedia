-- Prove2me | solution 1 for BurkholderDFI.NonnegPhi.stopped_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:32:22.822195+00:00
-- url     : https://prove2.me/submissions/1e15aa3f-3b98-4a62-8457-a3529eca8e47

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.NonnegPhi

open BurkholderDFI.SquareFnLp

lemma si_abs_le_of_maxFn_le {Ω : Type*} (f : ℕ → Ω → ℝ) (ω : Ω) {c : ℝ} (hc : 0 ≤ c)
    (h : maxFn f ω ≤ ENNReal.ofReal c) {n : ℕ} (hn : 1 ≤ n) : |f n ω| ≤ c := by
  have h1 : ENNReal.ofReal |f n ω| ≤ maxFnN f n ω := by
    unfold maxFnN
    exact le_iSup₂ (f := fun k (_ : k ∈ Finset.Icc 1 n) => ENNReal.ofReal |f k ω|) n
      (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have h2 : maxFnN f n ω ≤ maxFn f ω := le_iSup (fun n => maxFnN f n ω) n
  have := (h1.trans h2).trans h
  rwa [ENNReal.ofReal_le_ofReal_iff hc] at this

lemma si_exitTime_eq_top {Ω : Type*} (f : ℕ → Ω → ℝ) (ω : Ω) {c : ℝ}
    (h : ∀ n, 1 ≤ n → |f n ω| ≤ c) : exitTime f c ω = ⊤ := by
  unfold exitTime
  rw [iInf_eq_top]
  intro n
  rw [iInf_eq_top]
  rintro ⟨hn, hlt⟩
  exact absurd (h n hn) (not_le.mpr hlt)

theorem stopped_inclusion_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (β δ l : ℝ) (hδ : 0 < δ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < sqFn f ω ∧ maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal (β * l) < sqFnAt f (exitTime f (δ * l) ω - 1) ω} := by
  apply measure_mono
  intro ω ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq]
  have htop : exitTime f (δ * l) ω = ⊤ :=
    si_exitTime_eq_top f ω (fun n hn => si_abs_le_of_maxFn_le f ω (by positivity) h2 hn)
  have hts : (⊤ : ℕ∞) - 1 = ⊤ := by simpa using ENat.top_sub_natCast 1
  rw [htop, hts]
  simpa [sqFnAt] using h1

end BurkholderDFI.NonnegPhi

open BurkholderDFI.NonnegPhi


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (β δ l : ℝ) (hδ : 0 < δ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFn f ω ∧ BurkholderDFI.SquareFnLp.maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f (δ * l) ω - 1) ω} := by
  exact stopped_inclusion_core P f β δ l hδ hl
