-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.InvF.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:50.200838+00:00
-- url     : https://prove2.me/submissions/a53a15b6-516b-47f8-afb8-29948e9ae8a4

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace DiscreteGroups.sglob.LConvKM
namespace InvF
theorem _root_.solution {G : Type*} [Group G] {ρ : Representation ℂ G M} {B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ}
    (hB : InvF ρ B) {r : ℝ} (hr : 0 ≤ r) : InvF ρ ((r : ℂ) • B) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, hB.1 x y]
  · simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg hr (hB.2.1 x)
  · simp only [LinearMap.smul_apply, smul_eq_mul, hB.2.2 g x y]
end InvF
end DiscreteGroups.sglob.LConvKM
