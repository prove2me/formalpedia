-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.newton_cauchy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.45484+00:00
-- url     : https://prove2.me/submissions/549a20b7-fdeb-4470-bf5b-61f6f200f5cf

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
import Theorems.Thm_Formalism_IndefR_LocBrg_newton_step
import Theorems.Thm_Formalism_IndefR_LocBrg_newton_bound
import Theorems.Thm_Formalism_IndefR_LocBrg_pow_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)
namespace Formalism.IndefR.LocBrg
theorem _root_.solution (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) (n m : ℕ) (hnm : n ≤ m) :
    vv (newtonSq u m - newtonSq u n) ≤ vv (u - 1) ^ (n + 1) := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    have he : newtonSq u (m + 1) - newtonSq u n =
        (newtonSq u (m + 1) - newtonSq u m) + (newtonSq u m - newtonSq u n) := by ring
    rw [he]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ih)
    obtain ⟨h1, -⟩ := newton_bound u h2 hu m
    obtain ⟨-, -, hdiff⟩ := newton_step u m h1 h2
    rw [hdiff]
    exact le_trans (newton_bound u h2 hu m).2 (pow_anti hu.le (by omega))
end Formalism.IndefR.LocBrg
