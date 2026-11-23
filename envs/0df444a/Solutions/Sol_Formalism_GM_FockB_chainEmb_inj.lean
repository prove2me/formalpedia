-- Prove2me | solution 1 for Formalism.GM.FockB.chainEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:36.512078+00:00
-- url     : https://prove2.me/submissions/5791859a-0bea-48b7-b818-c3c2bcf08418

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FockB
theorem _root_.solution (t : ℕ) : Function.Injective (chainEmb N r t) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  rw [h.1, h.2]
end Formalism.GM.FockB
