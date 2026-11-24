-- Prove2me | solution 1 for Formalism.GM.gaussR_attained_least
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:41.146667+00:00
-- url     : https://prove2.me/submissions/0bb1ae4a-8914-4a5d-a87b-7c130100996b

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Theorems.Thm_Formalism_GM_gaussR_term_le
import Theorems.Thm_Formalism_GM_gaussR_attained

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]
namespace Formalism.GM
theorem _root_.solution (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ i₀, ‖P.coeff i₀‖₊ * ρ ^ i₀ = gaussR ρ P ∧
      ∀ i < i₀, ‖P.coeff i‖₊ * ρ ^ i < gaussR ρ P := by
  classical
  have h := gaussR_attained ρ P hP
  exact ⟨Nat.find h, Nat.find_spec h, fun i hi => lt_of_le_of_ne (gaussR_term_le ρ P i) (Nat.find_min h hi)⟩
end Formalism.GM
