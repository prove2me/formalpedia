-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.nEich_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:45.221727+00:00
-- url     : https://prove2.me/submissions/66672944-daf6-4269-b50c-a38f70b68e0e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_uh_of_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_nEich_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (ξ : Fin r → ℂ) :
    C2.nEich k r z ξ ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff]
  exact ⟨uh_of_herm _ _ (nEich_herm hz ξ), nEich_col hz ξ⟩
end Formalism.FourierDecayAlt.P.HermitianXiVector
