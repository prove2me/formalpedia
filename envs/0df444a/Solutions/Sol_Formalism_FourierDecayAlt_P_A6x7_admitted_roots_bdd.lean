-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.admitted.roots_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.605802+00:00
-- url     : https://prove2.me/submissions/2e844c62-314d-4fe1-a7bd-7d1b45f523ff

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_compact_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_admitted_pow_bdd

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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.admitted
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x7.admitted
theorem _root_.solution (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (s : ℕ)
    (hs : 1 ≤ s) (Q : Set K) (hQ : IsCompact Q) :
    ∃ C : Set K, IsCompact C ∧ ∀ z : K, z ^ s ∈ Q → z ∈ C := by
  obtain ⟨ϖ, hϖ, hϖ'⟩ := hD.unif
  obtain ⟨N, hN⟩ := pow_bdd hD h0 hϖ hϖ' s hs
  obtain ⟨n, hn⟩ := big hD hϖ hϖ' Q hQ
  refine ⟨_, compact_big hD ϖ (N + n), fun z hz => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have h1 : ((ϖ : K) ^ n * z) ^ (k + 1) ∈ R := by
    have e : ((ϖ : K) ^ n * z) ^ (k + 1) = ((ϖ : K) ^ n) ^ k * ((ϖ : K) ^ n * z ^ (k + 1)) := by
      rw [mul_pow, pow_succ ((ϖ : K) ^ n) k]; ring
    rw [e]; exact R.mul_mem (R.pow_mem (R.pow_mem hϖ n) k) (hn _ hz)
  have := hN _ h1
  show (ϖ : K) ^ (N + n) * z ∈ R
  rw [pow_add, mul_assoc]; exact this
end Formalism.FourierDecayAlt.P.A6x7.admitted
