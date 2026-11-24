-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_ordGe_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:51.2099+00:00
-- url     : https://prove2.me/submissions/3c65b498-039c-4998-a0ab-61b0cfb41103

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Theorems.Thm_Formalism_L2_Pj_Crude_div_ordGe_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_div_ordGe_one
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
theorem _root_.solution {a : ℕ} {f : PS k n d} (hf : OrdGe a f) (e : ℕ) : OrdGe (a * e) (f ^ e) := by
  induction e with
  | zero => simpa using div_ordGe_one
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact div_ordGe_mul ih hf
end Formalism.L2.Pj.Crude
