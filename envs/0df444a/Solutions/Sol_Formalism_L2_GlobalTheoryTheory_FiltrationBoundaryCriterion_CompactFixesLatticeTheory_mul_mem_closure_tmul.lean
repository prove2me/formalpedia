-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.mul_mem_closure_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:03:19.143954+00:00
-- url     : https://prove2.me/submissions/2b5267e9-53fd-4d0f-8a03-b6a1f05ab14d

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_CoordMulTmul
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_MemClosureOfMemSS

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
theorem _root_.solution {y z : AE F E}
    (hy : y ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a})
    (hz : z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a}) :
    y * z ∈ AddSubgroup.closure {y : AE F E | ∃ e ∈ intOE E, ∃ a ∈ intAd F, y = e ⊗ₜ[F] a} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨e, he, a, ha, rfl⟩ := hy
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨e', he', a', ha', rfl⟩ := hz
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, mul_mem he he', _, mul_mem ha ha', rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu
end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory
