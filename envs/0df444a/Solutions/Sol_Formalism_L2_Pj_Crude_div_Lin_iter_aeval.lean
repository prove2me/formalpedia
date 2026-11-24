-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_Lin_iter_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:45:37.179439+00:00
-- url     : https://prove2.me/submissions/685d3416-476c-464f-8c4f-729b711a0b86

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Theorems.Thm_Formalism_L2_Pj_Crude_div_Lin_aeval
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (t : ℕ) (Q : MvPolynomial ι k) :
    (Lin (cp l) (u l))^[t] (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ ((MvPolynomial.pderiv l)^[t] Q) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, div_Lin_aeval cp u φ l hl]
end Formalism.L2.Pj.Crude
