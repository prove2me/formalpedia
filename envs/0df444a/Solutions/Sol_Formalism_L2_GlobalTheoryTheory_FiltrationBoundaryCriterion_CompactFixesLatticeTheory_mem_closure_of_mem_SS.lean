-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mem_closure_of_mem_SS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:26.232205+00:00
-- url     : https://prove2.me/submissions/552472b3-7861-4676-8979-dc529ab32f64

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CoordMulTmul
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_mul_mem_closure_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
theorem _root_.solution {x : AE F E} (hx : x ∈ SS F E) :
    x ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨e, rfl⟩ | ⟨a, rfl⟩
    · exact AddSubgroup.subset_closure ⟨e, e.2, 1, one_mem _, rfl⟩
    · exact AddSubgroup.subset_closure ⟨1, one_mem _, a, a.2, rfl⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, rfl⟩
  | add y z _ _ hy hz => exact add_mem hy hz
  | neg y _ hy => exact neg_mem hy
  | mul y z _ _ hy hz => exact mul_mem_closure_tmul hy hz
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
