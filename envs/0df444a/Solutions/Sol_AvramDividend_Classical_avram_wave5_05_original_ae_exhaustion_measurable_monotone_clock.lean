-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:41:05.112768+00:00
-- url     : https://prove2.me/submissions/2f2e07ce-c45b-4bd6-b6e3-f5498c6917f1

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0∞) (hρ : Measurable ρ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSm : ∀ n, Measurable (S n))
    (hTailAE : ∀ᵐ ω ∂P,
      (⨆ n, (⨅ m, if n ≤ m then S m ω else ⊤)) = ⊤) :
    ∃ τ : ℕ → Ω → ℝ≥0∞,
      (∀ n, Measurable (τ n)) ∧
      (∀ ω, Monotone (fun n => τ n ω)) ∧
      (∀ ω, (⨆ n, τ n ω) = ρ ω) ∧
      (∀ n, ∀ᵐ ω ∂P, τ n ω ≤ min (ρ ω) (S n ω)) := by
  classical
  let R : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ⨅ m : ℕ, if n ≤ m then S m ω else ⊤
  have hRmeas (n : ℕ) : Measurable (R n) := by
    dsimp [R]
    apply Measurable.iInf
    intro m
    by_cases hnm : n ≤ m
    · simpa [hnm] using (hSm m)
    · simpa [hnm] using
        (measurable_const : Measurable (fun _ : Ω => (⊤ : ℝ≥0∞)))
  have hRmono (ω : Ω) : Monotone (fun n => R n ω) := by
    intro i j hij
    dsimp [R]
    apply le_iInf
    intro m
    by_cases hjm : j ≤ m
    · have him : i ≤ m := le_trans hij hjm
      simpa [hjm, him] using
        (iInf_le (fun k : ℕ => if i ≤ k then S k ω else ⊤) m)
    · simp [hjm]
  have hRleS (n : ℕ) (ω : Ω) : R n ω ≤ S n ω := by
    simpa [R] using
      (iInf_le (fun m : ℕ => if n ≤ m then S m ω else ⊤) n)
  have hSupMeas : Measurable (fun ω => ⨆ n, R n ω) :=
    Measurable.iSup hRmeas
  let good : Set Ω := {ω | (⨆ n, R n ω) = ⊤}
  have hGoodMeas : MeasurableSet good := by
    change MeasurableSet ((fun ω => ⨆ n, R n ω) ⁻¹' {⊤})
    exact hSupMeas (measurableSet_singleton _)
  let τ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if ω ∈ good then min (ρ ω) (R n ω) else ρ ω
  have hτmeas : ∀ n, Measurable (τ n) := by
    intro n
    exact Measurable.ite hGoodMeas
      (hρ.min (hRmeas n)) hρ
  have hτmono : ∀ ω, Monotone (fun n => τ n ω) := by
    intro ω i j hij
    by_cases hg : ω ∈ good
    · simpa [τ, hg] using min_le_min_left
        (ρ ω) (hRmono ω hij)
    · simp [τ, hg]
  have hτsup : ∀ ω, (⨆ n, τ n ω) = ρ ω := by
    intro ω
    by_cases hg : ω ∈ good
    · have hSupω : (⨆ n, R n ω) = ⊤ := hg
      calc
        (⨆ n, τ n ω) =
            (⨆ n, min (ρ ω) (R n ω)) := by
              simp [τ, hg]
        _ = min (ρ ω) (⨆ n, R n ω) := by
              rw [inf_iSup_eq]
        _ = ρ ω := by simp [hSupω]
    · simp [τ, hg]
  refine ⟨τ, hτmeas, hτmono, hτsup, ?_⟩
  intro n
  filter_upwards [hTailAE] with ω hω
  have hg : ω ∈ good := by simpa [good, R] using hω
  simpa [τ, hg] using min_le_min_left (ρ ω) (hRleS n ω)
