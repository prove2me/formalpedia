-- Prove2me | solution 1 for Formalism.L2.DIV.we_cut_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:15.215884+00:00
-- url     : https://prove2.me/submissions/30ec38ec-460a-4b76-bad0-aa24c6cd47cd

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord

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
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
namespace Formalism.L2.DIV
theorem _root_.solution {S S' : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)} (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν)
    (hS' : ∀ x ∈ S', x ∈ dualWeyl ℚ r n ν) (h : weCut r n ν S = weCut r n ν S') : S = S' := by
  ext x
  constructor
  · intro hx
    have h1 : (⟨x, hS x hx⟩ : dualWeyl ℚ r n ν) ∈ weCut r n ν S := hx
    rw [h] at h1
    exact h1
  · intro hx
    have h1 : (⟨x, hS' x hx⟩ : dualWeyl ℚ r n ν) ∈ weCut r n ν S' := hx
    rw [← h] at h1
    exact h1
end Formalism.L2.DIV
