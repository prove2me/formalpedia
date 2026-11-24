-- Prove2me | solution 1 for Formalism.REAL.unitary_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:07.896947+00:00
-- url     : https://prove2.me/submissions/672cbbdd-af7f-4135-a9ed-324b6adff8be

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Theorems.Thm_Formalism_REAL_rho_rhoN_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : UGap := by
  intro n ε lam g a b _ _ hg
  obtain ⟨d1, _⟩ := rho_rhoN_bound ε a
  obtain ⟨_, d2⟩ := rho_rhoN_bound ε b
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith
end Formalism.REAL
