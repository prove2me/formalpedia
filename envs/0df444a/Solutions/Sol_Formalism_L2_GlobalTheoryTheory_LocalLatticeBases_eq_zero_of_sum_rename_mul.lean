-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.eq_zero_of_sum_rename_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:56.946789+00:00
-- url     : https://prove2.me/submissions/82f480d4-bd77-4a15-ab0a-75703e439f21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_leftCoeff_rename_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
variable {K : Type*} [Field K]
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution {S₁ S₂ κ : Type*} [Fintype κ] (w : κ → MvPolynomial S₂ K) (hw : LinearIndependent K w)
    (a : κ → MvPolynomial S₁ K) (h : ∑ j, rename Sum.inl (a j) * rename Sum.inr (w j) = 0) : a = 0 := by
  funext j
  ext m
  have h' := congrArg (mvPolynomialCoeffInFirstVariables (K := K) (S₁ := S₁) (S₂ := S₂) m) h
  simp only [map_sum, leftCoeff_rename_mul, map_zero] at h'
  simpa using (Fintype.linearIndependent_iff.1 hw) (fun j => coeff m (a j)) h' j
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
