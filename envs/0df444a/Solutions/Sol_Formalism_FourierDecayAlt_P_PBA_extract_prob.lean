-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.extract_prob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:39.816669+00:00
-- url     : https://prove2.me/submissions/63671f41-19d6-4ec2-b02a-362657b3df84

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalNormNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt NumberField
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {ι X : Type} [Fintype ι] (U : Finset X) (θ : ℕ → ι → X → ℝ)
    (hθ : ∀ n A, TB.IsProb U (θ n A)) :
    ∃ (φ : ℕ → ℕ) (θ' : ι → X → ℝ), StrictMono φ ∧ (∀ A, TB.IsProb U (θ' A)) ∧
      ∀ A, ∀ x ∈ U, Tendsto (fun n => θ (φ n) A x) atTop (𝓝 (θ' A x)) := by
  classical
  let x : ℕ → (ι × U) → ℝ := fun n p => θ n p.1 p.2.1
  have hK : IsCompact (Set.Icc (0 : ι × U → ℝ) 1) := isCompact_Icc
  have hmem : ∀ n, x n ∈ Set.Icc (0 : ι × U → ℝ) 1 := by
    intro n
    refine ⟨fun p => (hθ n p.1).1 _, fun p => ?_⟩
    have h := Finset.single_le_sum (fun y _ => (hθ n p.1).1 y) p.2.2
    rw [(hθ n p.1).2.2] at h
    exact h
  obtain ⟨y, _, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hl : ∀ A z (h : z ∈ U), Tendsto (fun n => θ (φ n) A z) atTop (𝓝 (y (A, ⟨z, h⟩))) := fun A z h =>
    ((continuous_apply (A, (⟨z, h⟩ : U))).tendsto y).comp hlim
  refine ⟨φ, fun A z => if h : z ∈ U then y (A, ⟨z, h⟩) else 0, hφ, ?_, ?_⟩
  · intro A
    refine ⟨fun z => ?_, fun z hz => by simp [hz], ?_⟩
    · by_cases h : z ∈ U
      · simp only [h, dite_true]
        exact ge_of_tendsto' (hl A z h) fun n => (hθ (φ n) A).1 z
      · simp [h]
    · have hs : Tendsto (fun n => ∑ z ∈ U, θ (φ n) A z) atTop
          (𝓝 (∑ z ∈ U, if h : z ∈ U then y (A, ⟨z, h⟩) else 0)) := by
        apply tendsto_finsetSum
        intro z hz
        simp only [hz, dite_true]
        exact hl A z hz
      have h1 : (fun n => ∑ z ∈ U, θ (φ n) A z) = fun _ => (1 : ℝ) := funext fun n => (hθ (φ n) A).2.2
      rw [h1] at hs
      exact tendsto_nhds_unique hs tendsto_const_nhds
  · intro A z hz
    simp only [hz, dite_true]
    exact hl A z hz
end Formalism.FourierDecayAlt.P.PBA
