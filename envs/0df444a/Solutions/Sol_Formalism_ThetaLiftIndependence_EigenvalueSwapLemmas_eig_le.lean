-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.EigenvalueSwapLemmas.eig_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:51.456256+00:00
-- url     : https://prove2.me/submissions/1aa409b1-1bf9-4661-b285-8568049cf0eb

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_EigenSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.EigenvalueSwapLemmas
namespace Formalism.ThetaLiftIndependence.EigenvalueSwapLemmas
theorem _root_.solution {𝕜 E F : Type} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E)
    (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.finrank 𝕜 (Module.End.eigenspace (B ∘ₗ A) μ) ≤
      Module.finrank 𝕜 (Module.End.eigenspace (A ∘ₗ B) μ) := by
  have h : ∀ x ∈ Module.End.eigenspace (B ∘ₗ A) μ, A x ∈ Module.End.eigenspace (A ∘ₗ B) μ := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    simp only [LinearMap.comp_apply] at hx ⊢
    rw [hx, map_smul]
  refine LinearMap.finrank_le_finrank_of_injective (f := A.restrict h) ?_
  intro x y hxy
  have hx := (Module.End.mem_eigenspace_iff.1 x.2)
  have hy := (Module.End.mem_eigenspace_iff.1 y.2)
  have hA : A x = A y := congrArg Subtype.val hxy
  apply Subtype.ext
  have : μ • (x : E) = μ • (y : E) := by
    rw [← hx, ← hy]; simp [hA]
  exact smul_right_injective E hμ this
end Formalism.ThetaLiftIndependence.EigenvalueSwapLemmas
