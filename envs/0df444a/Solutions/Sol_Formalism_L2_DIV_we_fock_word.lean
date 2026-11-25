-- Prove2me | solution 1 for Formalism.L2.DIV.we_fock_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:25.119922+00:00
-- url     : https://prove2.me/submissions/a6bf8b3d-e3be-4032-b11a-350f2e1452db

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_we_applyWord_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_highest_weight
import Theorems.Thm_Formalism_GradedWeylDivisibility_fock_space_word_adjoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.DIV
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) (hP : P ∈ dualWeyl ℚ r n ν) :
    fockQ P (applyWord ℚ w (hw ℚ hn ν)) =
      eval (idFrame ℚ r n) (applyWord ℚ (transposeWord w) P) * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  rw [we_fock_symm, fock_space_word_adjoint r n w,
    fock_space_highest_weight r n hn ν hν _ (we_applyWord_mem ℚ r n ν _ P hP)]
end Formalism.L2.DIV
