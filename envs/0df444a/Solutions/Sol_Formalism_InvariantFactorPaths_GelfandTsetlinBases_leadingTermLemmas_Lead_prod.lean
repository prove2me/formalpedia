-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.Lead_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:15.753954+00:00
-- url     : https://prove2.me/submissions/f2174442-eac6-43a9-bdb8-b87f0ba6f34f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_Lead_one
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_Lead_mul

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)
variable {κ}
variable {R : Type*} [CommRing R] (κ)
variable {κ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (hκ : Function.Injective κ) {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R)
    (d : ι → σ →₀ ℕ) (h : ∀ c ∈ s, Lead κ (f c) (d c)) : Lead κ (∏ c ∈ s, f c) (∑ c ∈ s, d c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lead_one : Lead κ (1 : MvPolynomial σ R) 0)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact Lead_mul hκ (h a (Finset.mem_insert_self a s))
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
