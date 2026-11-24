-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CSym.genE_FFam_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:16.147813+00:00
-- url     : https://prove2.me/submissions/c0788e00-8d20-4bc8-8c4f-681d7f54b96e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_ArtinHasse_ArtinHasseProofs_SymmSeries
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_GaussElementarySymmetric

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
open CSym
open Formalism.InvariantFactorPaths.G7.CSym
namespace Formalism.InvariantFactorPaths.G7.CSym
theorem _root_.solution {K : Type} [Field K] (Q : K) (t : ℕ) (m : ℕ → K) (j : ℕ) :
    genE (FFam Q t m (j + 1)) =
      genE (fun x => m (j + 1) * beFam Q (t + 1) x) * genE (FFam Q t m j) := by
  unfold genE
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Fin.prod_univ_castSucc, mul_comm]
  rfl
end Formalism.InvariantFactorPaths.G7.CSym
