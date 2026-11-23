-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.X_inl_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:14.535579+00:00
-- url     : https://prove2.me/submissions/4dcb3d3f-37e2-4aba-9a43-26041226862a

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_monomial_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_lin_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_add
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_inl
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_yDeg_inl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    X (Sum.inl i) * f ∈ PolAB K k (A + 1) B := by
  have key := lin_mem (A := A) (B := B) (LinearMap.mulLeft K (X (Sum.inl i) : PolXY K k))
    (PolAB K k (A + 1) B) (fun m c hx hy => by
      rw [LinearMap.mulLeft_apply,
        show (X (Sum.inl i) : PolXY K k) = monomial (Finsupp.single (Sum.inl i) 1) 1 from rfl,
        monomial_mul, one_mul]
      exact monomial_mem _ (by rw [xDeg_add, xDeg_inl]; omega) (by rw [yDeg_add, yDeg_inl]; omega)) hf
  simpa only [LinearMap.mulLeft_apply] using key
end Formalism.CountingSumsFrames.Har2
