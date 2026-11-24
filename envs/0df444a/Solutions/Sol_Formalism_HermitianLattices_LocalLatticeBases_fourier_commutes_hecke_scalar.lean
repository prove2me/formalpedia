-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.fourier_commutes_hecke_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:45.577978+00:00
-- url     : https://prove2.me/submissions/90575f56-0da7-4eeb-99cf-378602905836

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : FourierCommutesHeckeScalar := by
  intro R _ M M' _ _ _ _ U D G U' D' G' K c a a' h1 h2 h3 h4
  calc a' • (K ∘ₗ D ∘ₗ G) = (a' • LinearMap.id) ∘ₗ (K ∘ₗ D ∘ₗ G) := by ext; simp
    _ = D' ∘ₗ (U' ∘ₗ K) ∘ₗ D ∘ₗ G := by rw [← h2]; rfl
    _ = c • (D' ∘ₗ K ∘ₗ (U ∘ₗ D) ∘ₗ G) := by rw [h1]; ext; simp
    _ = (c * a) • (D' ∘ₗ (K ∘ₗ G)) := by rw [h3]; ext; simp [mul_smul]
    _ = _ := by rw [h4]
end Formalism.HermitianLattices.LocalLatticeBases
