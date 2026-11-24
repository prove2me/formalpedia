-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:52.736345+00:00
-- url     : https://prove2.me/submissions/c08d1710-c7e8-4ede-998f-3fc99f69bf5b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_indexChange_one
import Theorems.Thm_Formalism_DivisionValues_indexChange_mul
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_Dg
import Theorems.Thm_Formalism_DivisionValues_indexChange_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) (g : Fin d → K) (hg : ∀ k, g k ≠ 0) :
    IdxChangeP v (Matrix.diagonal g) := by
  suffices h : ∀ s : Finset (Fin d), IdxChangeP v (Matrix.diagonal fun k => if k ∈ s then g k else 1)
    by simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using indexChange_one (K := K) (d := d) v
  | insert i s hi ih =>
    have heq : Matrix.diagonal (fun k => if k ∈ insert i s then g k else 1) =
        Matrix.diagonal (fun k => if k ∈ s then g k else 1) * idxChangeDg i (g i) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp [hi]
      · simp [hk]
    rw [heq]
    refine indexChange_mul v ?_ (by rw [idxChange_det_Dg]; exact hg i) ih (indexChange_scalar v i (hg i))
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by
      split_ifs
      · exact hg k
      · exact one_ne_zero
end Formalism.DivisionValues
