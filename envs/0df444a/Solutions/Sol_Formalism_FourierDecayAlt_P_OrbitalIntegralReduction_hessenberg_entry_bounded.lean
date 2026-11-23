-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.hessenberg_entry_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:58.518089+00:00
-- url     : https://prove2.me/submissions/158a465d-9309-4662-90e4-c457e0d5f398

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hϖ : (ϖ : K) ∈ R) {m : ℕ} {t ρ : K} {x : Fin m → K} {y : Pr (m + 1) → K}
    (ht : Bd R ϖ a t) (hx : ∀ k, Bd R ϖ a (x k)) (i : Fin (m + 1)) (j : Fin m)
    (hy : ∀ h : i < j.succ, Bd R ϖ a (y ⟨(i, j.succ), h⟩)) :
    Bd R ϖ a (HH t (Fin.cons ρ x : Fin (m + 1) → K) y i j.succ) := by
  unfold HH
  split_ifs with h1 h2 h3
  · rw [h1, Fin.cons_succ]; exact hx j
  · exact hy h2
  · exact ht
  · exact Bd.of_mem hϖ R.zero_mem a
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
