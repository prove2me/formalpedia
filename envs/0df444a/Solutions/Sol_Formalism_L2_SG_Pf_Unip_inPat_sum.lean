-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.inPat_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:45.203989+00:00
-- url     : https://prove2.me/submissions/99fe1817-7169-4597-94f7-940900efc23a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {α : Type*} {s : Finset α} {f : α → Matrix ι ι K} (h : ∀ a ∈ s, InPat lv k (f a)) :
    InPat lv k (∑ a ∈ s, f a) := by
  intro i j hij
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun a ha => h a ha i j hij
end Formalism.L2.SG.Pf.Unip
