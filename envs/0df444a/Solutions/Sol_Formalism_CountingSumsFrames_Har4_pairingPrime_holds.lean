-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.pairingPrime_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:44.716884+00:00
-- url     : https://prove2.me/submissions/5efd38b3-cfdd-4fb5-8a8b-4181195a5f21

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

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
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution : HPrime := by
  intro F _ k hk
  classical
  have hirr : Irreducible (hXY F k) := by
    have h := MvPolynomial.irreducible_sumSMulXSMulY (R := F) (n := Fin k)
      (Finsupp.equivFunOnFinite.symm (fun _ => (1:F))) ?_ ?_
    · convert h using 1
      simp [hXY, sumSMulXSMulY, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · refine ⟨⟨0, by omega⟩, by simp, ⟨1, by omega⟩, by simp, ?_⟩
      simp [Fin.ext_iff]
    · intro r hr
      exact isUnit_of_dvd_one (by simpa using hr ⟨0, by omega⟩)
  exact hirr.prime
end Formalism.CountingSumsFrames.Har4
