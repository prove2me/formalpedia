-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bs_dual_le_weyl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:15.222867+00:00
-- url     : https://prove2.me/submissions/8447fca6-5442-4fb5-8d7a-762efd13eada

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_bs_map_weyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylEqNablaQ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    dualWeyl ℂ r n ν ≤ weyl ℂ r n hn ν := by
  rw [standardMonomialSpanDomain ℂ r n ν, Submodule.span_le]
  rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
  rw [← ldlat_map_bidet (algebraMap ℚ ℂ)]
  apply bs_map_weyl
  rw [weylEqNablaQ r n hn ν hν, ← hsh]
  exact bidetMem ℚ r n K sz hsz I
end Formalism.BranchingDeterminantCap
