-- Prove2me | solution 1 for Formalism.ZRN.e_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:11.808517+00:00
-- url     : https://prove2.me/submissions/2efd6c61-bdc1-42e0-b467-6a1d1e3b5e83

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (n : ℕ) : Differentiable ℂ (e n) := by
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  intro s
  unfold e
  fun_prop (disch := simp [h1, h2])
end Formalism.ZRN
