-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_stopping_from_variable_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:59:43.15399+00:00
-- url     : https://prove2.me/submissions/714ba13d-0dac-404e-b6e2-b338cdadf6f5

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_bounded_mesh_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_ja18_sampled_ceiling_is_original_stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Sample the original filtration, lift each sampled stopping ceiling to
the original clock, and squeeze its physical time error to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (n : ℕ) (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (e : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ) (δ : ℕ → ℝ≥0)
    (he : ∀ k, Monotone (e k))
    (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k)
    (hTop : ∀ k, e k (N k) = (n : ℝ≥0))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k, ∃ S : Finset ℝ≥0, ∀ ω, ρ k ω ∈ S) ∧
      (∀ k ω, τ ω ≤ ρ k ω) ∧
      (∀ k ω, ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) := by
  classical
  let G (k : ℕ) : Filtration ℕ mΩ :=
    { seq := fun i => 𝓕.rightCont (e k i)
      mono' := by
        intro i j hij
        exact 𝓕.rightCont.mono ((he k) hij)
      le' := by
        intro i
        exact 𝓕.rightCont.le (e k i) }
  have hExists (k : ℕ) :
      ∃ K : Ω → ℕ,
        IsStoppingTime (G k) (fun ω => (K ω : WithTop ℕ)) ∧
        (∀ ω, (K ω : WithTop ℕ) ≤ (N k : WithTop ℕ)) ∧
        (∀ ω, τ ω ≤ e k (K ω) ∧ e k (K ω) ≤ τ ω + δ k) := by
    apply avram_ja18_original_bounded_mesh_ceiling τ hτ (e k) (he k)
      (N k) ?_ (δ k) (h0 k) (hStep k) (G k) rfl
    intro ω
    simpa only [hTop k] using hBound ω
  choose K hStopK hBoundK hApproxK using hExists
  let ρ : ℕ → Ω → ℝ≥0 := fun k ω => e k (K k ω)
  refine ⟨ρ, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    apply avram_ja18_sampled_ceiling_is_original_stopping (e k) (he k) (K k)
    intro i
    have h := hStopK k i
    change MeasurableSet[𝓕.rightCont (e k i)]
      {ω : Ω | (K k ω : WithTop ℕ) ≤ (i : WithTop ℕ)} at h
    simpa using h
  · intro k
    refine ⟨Finset.image (e k) (Finset.range (N k + 1)), ?_⟩
    intro ω
    have hi : K k ω ≤ N k := by exact_mod_cast hBoundK k ω
    exact Finset.mem_image.mpr ⟨K k ω,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
  · intro k ω
    exact (hApproxK k ω).1
  · intro k ω
    have hi : K k ω ≤ N k := by exact_mod_cast hBoundK k ω
    exact ((he k) hi).trans (le_of_eq (hTop k))
  · intro ω
    have hUpper : Tendsto (fun k => τ ω + δ k) atTop (𝓝 (τ ω)) := by
      simpa using (tendsto_const_nhds.add hδ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hUpper
    · exact Filter.Eventually.of_forall (fun k => (hApproxK k ω).1)
    · exact Filter.Eventually.of_forall (fun k => (hApproxK k ω).2)
