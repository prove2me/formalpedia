-- Prove2me | solution 1 for Formalism.L2.Th1.E.AddThm.rat_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:12.719332+00:00
-- url     : https://prove2.me/submissions/42914cbd-7998-4b4e-8ceb-39368c3208fd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ExistsFinitePartOneIdeleSplitCongruenceQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.AddThm
open Formalism.L2.Th1
variable (L : PeriodPair)
namespace Formalism.L2.Th1.E.AddThm
theorem _root_.solution (q : ℚ) (hq : q.den ≠ 1) (x : ℂ) (hx : x = (q : ℂ) * L.ω₁) : x ∉ L.lattice := by
  intro h
  have h' := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := q) (β := 0)).1
    (by rw [hx] at h; simpa using h)
  exact hq h'.1
end Formalism.L2.Th1.E.AddThm
