-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.prod_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:55.516723+00:00
-- url     : https://prove2.me/submissions/6f88f598-b024-4dd5-85ad-38c3adc01b8b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution {ι : Type} {μ : K} (hμ : μ ∈ R) (S : Finset ι) (w u : ι → K)
    (hu : ∀ i ∈ S, ∃ ρ ∈ R, u i = μ * ρ) (hw : ∀ i ∈ S, ∃ e ∈ R, w i = 1 - u i + μ ^ 2 * e) :
    ∃ ρ ∈ R, ∃ σ ∈ R, ∑ i ∈ S, u i = μ * σ ∧ ∏ i ∈ S, w i = 1 - ∑ i ∈ S, u i + μ ^ 2 * ρ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, R.zero_mem, 0, R.zero_mem, by simp, by simp⟩
  | insert i S hi ih =>
    obtain ⟨ρ, hρ, σ, hσ, e1, e2⟩ := ih (fun k hk => hu k (Finset.mem_insert_of_mem hk))
      (fun k hk => hw k (Finset.mem_insert_of_mem hk))
    obtain ⟨ρi, hρi, e3⟩ := hu i (Finset.mem_insert_self _ _)
    obtain ⟨ei, hei, e4⟩ := hw i (Finset.mem_insert_self _ _)
    refine ⟨ρi * σ + ρ - μ * ρi * ρ + ei * (1 - μ * σ + μ ^ 2 * ρ), ?_, ρi + σ, R.add_mem hρi hσ, ?_, ?_⟩
    · exact R.add_mem (R.sub_mem (R.add_mem (R.mul_mem hρi hσ) hρ) (R.mul_mem (R.mul_mem hμ hρi) hρ))
        (R.mul_mem hei (R.add_mem (R.sub_mem R.one_mem (R.mul_mem hμ hσ))
          (R.mul_mem (R.pow_mem hμ 2) hρ)))
    · rw [Finset.sum_insert hi, e1, e3]; ring
    · rw [Finset.sum_insert hi, Finset.prod_insert hi, e2, e4, e1, e3]; ring
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
