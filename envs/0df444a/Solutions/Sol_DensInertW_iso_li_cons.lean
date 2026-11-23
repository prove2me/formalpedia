-- Prove2me | solution 1 for DensInertW.iso_li_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:06.570822+00:00
-- url     : https://prove2.me/submissions/1ecddba4-d1eb-4e20-9705-32629aeb9f91

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
theorem _root_.solution {n c : ℕ} (x : Fin n → L) (U : Fin c → Fin n → L) (a : Fin c → L)
    (φ : (Fin n → L) →ₗ[L] L) (hφx : φ x = 1) (hφU : ∀ i, φ (U i) = 0)
    (hU : LinearIndependent L U) :
    LinearIndependent L (Fin.cons x (fun i => U i + a i • x) : Fin (c + 1) → Fin n → L) := by
  rw [Fintype.linearIndependent_iff] at hU ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have h1 := congrArg φ hg
  simp only [map_add, map_sum, map_smul, hφx, hφU, smul_eq_mul, mul_one, add_zero, mul_add, mul_zero,
    map_zero] at h1
  have h2 : ∑ i, g i.succ • U i = 0 := by
    have e : ∑ i, g i.succ • U i + (g 0 + ∑ i, g i.succ * a i) • x = 0 := by
      rw [← hg]
      simp only [smul_add, Finset.sum_add_distrib, add_smul, Finset.sum_smul, smul_smul]
      abel
    have h1' : g 0 + ∑ i, g i.succ * a i = 0 := by simpa using h1
    rw [h1', zero_smul, add_zero] at e
    exact e
  have hs := hU _ h2
  intro i
  refine Fin.cases ?_ (fun j => hs j) i
  simpa [hs] using h1
end DensInertW
