-- Prove2me | solution 1 for Formalism.GM.TM.existsAdaptedBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:28.78082+00:00
-- url     : https://prove2.me/submissions/2cba8144-57bf-40ee-bfc0-a7f7897a78d7

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_adapted_of_fg
import Theorems.Thm_Formalism_GM_TM_mmwZ_fg

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
theorem _root_.solution : AdaptedBasisExists := by
  intro p _ K r _ LLw q J M ρ w
  refine adapted_of_fg (MMwZ p LLw J M ρ w) (Fin.last K, ρ) (mmwZ_fg LLw J M ρ w) (LLw.deg (Fin.last K)) ?_
  intro x hx m hm
  have hxY := (Submodule.mem_inf.mp hx).1
  have hxP : x ∈ Pol p r LLw := (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hxY).1).1).1
  rw [Pol, mem_restrictSupport_iff] at hxP
  have hmd : MultiDeg LLw m := hxP (Finset.mem_coe.mpr hm)
  rw [← hmd (Fin.last K)]
  exact Finset.single_le_sum (f := fun c => m (Fin.last K, c)) (fun _ _ => Nat.zero_le _) (mem_univ ρ)
end Formalism.GM.TM
