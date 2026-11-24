-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:49.221479+00:00
-- url     : https://prove2.me/submissions/854e0388-d951-4952-a944-094659f0c299

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_CX
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_CC_mul_X

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution [Fintype κ] (b : κ → ι → K) (x : ι) : BiLe (Finsupp.single x 1)
    (MvPolynomial.C (MvPolynomial.X x) +
      ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
        MvPolynomial κ (MvPolynomial ι K)) :=
  biLe_add (biLe_CX x) (biLe_sum _ _ (fun k _ => biLe_CC_mul_X x (b k x) k))
end Formalism.InvariantFactorPaths.G7
