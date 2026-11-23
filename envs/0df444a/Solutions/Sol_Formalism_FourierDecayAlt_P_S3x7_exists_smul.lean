-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.exists_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:59.490543+00:00
-- url     : https://prove2.me/submissions/0f2853fe-de8a-44a8-8a6e-d613e1d534b2

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {ϖ : o} (hϖ : Irreducible ϖ) {m n : Type} (Z : Matrix m n o)
    (hZ : Z.map (IsLocalRing.residue o) = 0) : ∃ W : Matrix m n o, Z = ϖ • W := by
  have h : ∀ a b, ∃ w, Z a b = ϖ * w := by
    intro a b
    have h0 : IsLocalRing.residue o (Z a b) = 0 := congrFun (congrFun hZ a) b
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h0
    exact h0
  choose W hW using h
  exact ⟨Matrix.of W, by ext a b; simpa using hW a b⟩
end Formalism.FourierDecayAlt.P.S3x7
