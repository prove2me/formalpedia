-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.witt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:43.480307+00:00
-- url     : https://prove2.me/submissions/f5b123a8-ee93-4cad-a836-aca6789db5f0

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_witt_extension_induction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hσ : Inv σ) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h) (hn : Nondeg h) {a : ℕ} (x y : Fin a → V)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, h (x i) (x j) = h (y i) (y j)) :
    ∃ g : V ≃ₗ[K] V, (∀ u v, h (g u) (g v) = h u v) ∧ ∀ i, g (x i) = y i := by
  have h1 := hx.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h1
  exact witt_extension_induction hσ h hh hn (finrank K V - a) a x y (by omega) hx hy hxy
end Formalism.FourierDecayAlt.P.S3x6
