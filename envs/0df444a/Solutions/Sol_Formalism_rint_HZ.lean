-- Prove2me | solution 1 for Formalism.rint_HZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:31.311795+00:00
-- url     : https://prove2.me/submissions/fd367c18-3186-427a-9aa1-7165400f53d7

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_rint_Gz


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
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1) {σ : ℝ}
    (hσ : 1 < σ) : IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by
  have a1 := rint_Gz h3 h5 hσ
  have a4 := h5.1 θ σ (by linarith)
  have hfun : (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) = fun x =>
      ε * (Gz x * x ^ (-σ - 1)) + C * (x ^ θ * x ^ (-σ - 1)) := by
    funext x
    simp only [HZ]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.const_mul a1 _) (Integrable.const_mul a4 _)
end Formalism
