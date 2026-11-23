-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.hs_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:01.127485+00:00
-- url     : https://prove2.me/submissions/ae22778f-2203-4d0c-9247-9b201875c421

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_hs_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : hs (kᴴ * y * k) = hs y := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  apply Complex.ofReal_injective
  rw [hs_eq_trace, hs_eq_trace]
  have : kᴴ * y * k * (kᴴ * y * k)ᴴ = kᴴ * (y * yᴴ * k) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc k kᴴ, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]
end CompanionTheory.D.gk.admitted.Gard
