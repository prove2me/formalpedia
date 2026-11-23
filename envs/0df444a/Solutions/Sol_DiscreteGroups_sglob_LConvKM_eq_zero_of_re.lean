-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.eq_zero_of_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:04.762504+00:00
-- url     : https://prove2.me/submissions/4025a2e4-0af0-47d2-8414-9bca1ee51fad

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_apply_eq_zero_of_re

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
variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (xs : ℕ → M) (hsp : Submodule.span ℂ (Set.range xs) = ⊤)
    (h : ∀ i, (B (xs i) (xs i)).re = 0) (x y : M) : B x y = 0 := by
  have hle : Submodule.span ℂ (Set.range xs) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    ext z
    rw [LinearMap.zero_apply]
    exact apply_eq_zero_of_re B herm psd (xs i) (h i) z
  have hx : x ∈ LinearMap.ker B := hle (by rw [hsp]; exact Submodule.mem_top)
  rw [LinearMap.mem_ker] at hx
  rw [hx, LinearMap.zero_apply]
end DiscreteGroups.sglob.LConvKM
