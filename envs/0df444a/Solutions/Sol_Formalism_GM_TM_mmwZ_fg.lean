-- Prove2me | solution 1 for Formalism.GM.TM.mmwZ_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:16.733814+00:00
-- url     : https://prove2.me/submissions/119a8ea5-29c5-4688-a9b5-b8cd3188cda5

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_polZ_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution {K r : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) : (MMwZ p LLw J M ρ w).FG := by
  refine Submodule.FG.of_le (polZ_fg LLw) ?_
  intro x hx
  have hxY := (Submodule.mem_inf.mp hx).1
  exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hxY).1).1).1,
    (Submodule.mem_inf.mp hx).2⟩
end Formalism.GM.TM
