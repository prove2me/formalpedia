-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.exists_lat_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:30.193986+00:00
-- url     : https://prove2.me/submissions/c1d5df2f-0d18-4048-a6fa-32b7917f0348

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_lat_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution {ι : Type} (I : Finset ι) (M : ι → AddSubgroup K)
    (hM : ∀ i ∈ I, IsOpen (M i : Set K)) {Λ : AddSubgroup K} (hΛ : IsLat Λ) :
    ∃ Λ' : AddSubgroup K, IsLat Λ' ∧ Λ' ≤ Λ ∧ ∀ i ∈ I, Λ' ≤ M i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨Λ, hΛ, le_rfl, by simp⟩
  | insert a I ha ih =>
    obtain ⟨Λ', h1, h2, h3⟩ := ih (fun i hi => hM i (Finset.mem_insert_of_mem hi))
    refine ⟨Λ' ⊓ M a, lat_inf h1 (hM a (Finset.mem_insert_self _ _)), inf_le_left.trans h2, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact inf_le_right
    · exact inf_le_left.trans (h3 i hi)
end Formalism.FourierDecayAlt.P.GermSumLattices
