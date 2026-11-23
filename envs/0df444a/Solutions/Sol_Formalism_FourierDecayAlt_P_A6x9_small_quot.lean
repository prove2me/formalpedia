-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.small_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:23.457837+00:00
-- url     : https://prove2.me/submissions/5a636205-90fb-4dd6-acd4-d66351e80f5b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_mem_mulR

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
include hπ hk'
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution {b : K} (hb : b ∈ mulR R ((π : K) ^ (k + 1 + k' + i))) :
    b * z0i ∈ mulR R ((π : K) ^ (k + 1)) := by
  obtain ⟨r, hr, rfl⟩ := mem_mulR.1 hb
  exact mem_mulR.2 ⟨(π : K) ^ i * ((π : K) ^ k' * z0i) * r,
    R.mul_mem (R.mul_mem (R.pow_mem hπ i) hk') hr, by ring⟩
end Formalism.FourierDecayAlt.P.A6x9
