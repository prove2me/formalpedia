-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:12:32.781823+00:00
-- url     : https://prove2.me/submissions/7fa1e442-76cf-4895-bac5-08b1adad0186

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
theorem _root_.solution (O : Subring K) {p q r s : K} (hp : p ∈ O) (hq : q ∈ O) (hr : r ∈ O) (hs : s ∈ O) (β a : Fin 4) :
    qM p q r s β a ∈ O := by
  fin_cases β <;> fin_cases a <;> simp [qM, hp, hq, hr, hs]
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
