-- Prove2me | solution 1 for Formalism.zetaLandauEps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:45.330873+00:00
-- url     : https://prove2.me/submissions/b9453e86-e0c7-47d8-91f3-84f4a5e80ea7

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_zetaLandau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution : ZetaLandauEps := by
  intro s₀ hs₀ θ hθ0 hθ1 hB s hs
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ θ + ε < s.re ∧ θ + ε < 1 := by
    refine ⟨min ((s.re - θ) / 2) ((1 - θ) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left ((s.re - θ) / 2) ((1 - θ) / 2); linarith
    · have := min_le_right ((s.re - θ) / 2) ((1 - θ) / 2); linarith
  exact zetaLandau s₀ hs₀ (θ + ε) (by linarith) hε2 (hB ε hε0) s hε1
end Formalism
