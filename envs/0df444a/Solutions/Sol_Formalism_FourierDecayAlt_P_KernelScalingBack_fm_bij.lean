-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.fm_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:13.333612+00:00
-- url     : https://prove2.me/submissions/9107c86b-a7b6-4627-851d-ef06cc9d1eb2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_fm_surj
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_toCos_fm_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inv_toCos_rep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
variable (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)
include hc
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution : Function.Bijective (fun q : Cos R ((S, T) : Point K) =>
    A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c (rep R q))) := by
  constructor
  · intro q q' h
    have h1 := (toCos_fm_iff R S T c hc _ _).1 h
    rwa [A5x8.inv_toCos_rep, A5x8.inv_toCos_rep] at h1
  · intro q₁
    obtain ⟨p, hp⟩ := fm_surj S T c (rep R q₁)
    refine ⟨A5x8.toCos R (w := ((S, T) : Point K)) p, ?_⟩
    show A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c (rep R (A5x8.toCos R (w := ((S, T) : Point K)) p))) = q₁
    rw [(toCos_fm_iff R S T c hc _ p).2 (A5x8.inv_toCos_rep R _), hp, A5x8.inv_toCos_rep]
end Formalism.FourierDecayAlt.P.KernelScalingBack
