-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.hb1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:44.700806+00:00
-- url     : https://prove2.me/submissions/af0aad5f-d86e-49b7-a711-335dc0e1d242

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_mulR_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_pow_diff0
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_one_add_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_small_quot

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
variable (hd : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
  (hπ : (π : K) ∈ R) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {m k k' i : ℕ} {si z0 z0i : K}
  (hs : ((m + 1 : ℕ) : K) * si = 1) (hk : (π : K) ^ k * si ∈ R) (hz0 : z0 * z0i = 1)
  (hk' : (π : K) ^ k' * z0i ∈ R)
include hπ hs hk hz0 hk'
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution {z : K} (hz : z - z0 ∈ mulR R ((π : K) ^ (k + 1 + k' + i))) :
    ∃ b ∈ mulR R ((π : K) ^ (k + 1 + k' + i)),
      z ^ (m + 1) - z0 ^ (m + 1) = ((m + 1 : ℕ) : K) * z0 ^ m * b := by
  obtain ⟨e, he, h⟩ := pow_diff0 π hπ hs hk (small_quot π hπ hk' hz)
  refine ⟨(z - z0) * (1 + e), mulR_mul hz (one_add_mem π hπ he), ?_⟩
  have e1 : z = z0 * (1 + (z - z0) * z0i) := by linear_combination (z0 - z) * hz0
  have e2 : z ^ (m + 1) = z0 ^ (m + 1) * (1 + (z - z0) * z0i) ^ (m + 1) := by
    rw [← mul_pow, ← e1]
  rw [e2]
  linear_combination z0 ^ (m + 1) * h +
    ((m + 1 : ℕ) : K) * z0 ^ m * (z - z0) * (1 + e) * hz0
end Formalism.FourierDecayAlt.P.A6x9
