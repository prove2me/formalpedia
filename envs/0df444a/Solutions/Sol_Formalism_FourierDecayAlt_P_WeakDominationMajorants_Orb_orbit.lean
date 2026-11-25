-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:27.54621+00:00
-- url     : https://prove2.me/submissions/d37935ca-9bd0-4751-bcb6-563f182d7152

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_orbit_constant_thirteen_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_both_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_ld_eq_Dmin
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_det_eq_Dmin
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_continuous_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_continuous_ld
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_continuous_detZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_gN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix
open Matrix
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakDominationMajorants Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (K : Set (Mat k r)) (hK : IsCompact K)
    (hKO : K ⊆ Om k r z z') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      gN n ≤ C * gN (n⁻¹ * g * n') ^ (2 * r + 1) ∧ gN n' ≤ C * gN (n⁻¹ * g * n') ^ (2 * r + 1) := by
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn continuous_gN.continuousOn).bddAbove
  have hΓ : 1 ≤ max 1 M := le_max_left _ _
  have hDne : ∀ g ∈ K, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0 := fun g hg => (hKO hg).2.1

  obtain ⟨δ1, hδ1, hδ1K⟩ : ∃ δ1 : ℝ, 0 < δ1 ∧ ∀ g ∈ K, ∀ b : Fin r, δ1 ≤ ‖ld (Zm g) b‖ := by
    have hS : IsCompact (K ×ˢ (Set.univ : Set (Fin r))) := hK.prod isCompact_univ
    have hf : Continuous (fun p : Mat k r × Fin r => ‖ld (Zm p.1) p.2‖) :=
      continuous_prod_of_discrete_right.2 fun b => (continuous_ld b).norm
    by_cases hne : (K ×ˢ (Set.univ : Set (Fin r))).Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := hS.exists_isMinOn hne hf.continuousOn
      refine ⟨‖ld (Zm p0.1) p0.2‖, ?_, fun g hg b => ?_⟩
      · rw [norm_pos_iff, ld_eq_Dmin z z']
        exact hDne p0.1 hp0.1 _ (by show p0.2.val + 1 ≤ r; have := p0.2.isLt; omega)
      · have hgb : (g, b) ∈ K ×ˢ (Set.univ : Set (Fin r)) := ⟨hg, Set.mem_univ _⟩
        exact isMinOn_iff.mp hmin (g, b) hgb
    · refine ⟨1, one_pos, fun g hg b => absurd ⟨(g, b), hg, Set.mem_univ _⟩ hne⟩
  obtain ⟨δ2, hδ2, hδ2K⟩ : ∃ δ2 : ℝ, 0 < δ2 ∧ ∀ g ∈ K, δ2 ≤ ‖(Zm g).det‖ := by
    by_cases hne : K.Nonempty
    · obtain ⟨g0, hg0, hmin⟩ := hK.exists_isMinOn hne continuous_detZ.norm.continuousOn
      refine ⟨‖(Zm g0).det‖, ?_, fun g hg => isMinOn_iff.mp hmin g hg⟩
      rw [norm_pos_iff, det_eq_Dmin z z']
      exact hDne g0 hg0 _ (by show r ≤ r; exact le_rfl)
    · exact ⟨1, one_pos, fun g hg => absurd ⟨g, hg⟩ hne⟩
  have hδ : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * c13 k r (max 1 M) (min δ1 δ2),
    by have := orbit_constant_thirteen_nonneg (k := k) (r := r) hΓ hδ; positivity, ?_⟩
  intro g hg n hn n' hn'
  have hgM : gN g ≤ max 1 M := (hM (Set.mem_image_of_mem _ hg)).trans (le_max_right _ _)
  exact both_bd hΓ hδ (hKO hg).1 hgM
    (fun b => (min_le_left _ _).trans (hδ1K g hg b)) ((min_le_right _ _).trans (hδ2K g hg)) hn hn'
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
