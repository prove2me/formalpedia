-- Prove2me | solution 1 for DensInertW.iso_li_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:14.428646+00:00
-- url     : https://prove2.me/submissions/b850c784-c7ad-4e7d-8f59-7a61d0d34539

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_IsoPeel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]
namespace DensInertW
theorem _root_.solution {n c : ℕ} (x : Fin n → L) (X' : Fin c → Fin n → L) (a : Fin c → L)
    (h : LinearIndependent L (Fin.cons x X' : Fin (c + 1) → Fin n → L)) :
    LinearIndependent L (fun i => X' i - a i • x) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have := h (Fin.cons (-(∑ j, g j * a j)) g) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hg]
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, neg_smul]
    abel) i.succ
  simpa using this
end DensInertW
