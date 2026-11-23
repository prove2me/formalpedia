-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.card_unit_norm_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:13.952862+00:00
-- url     : https://prove2.me/submissions/91d075b0-1586-4aae-bb2c-641b39a61be7

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_orthonormal
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_norm_orthonormal_coords

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
theorem _root_.solution (hσ : Inv σ) [Finite K] (s : ℕ → ℕ)
    (hs : ∀ n, Nat.card {w : Fin n → K // ∑ i, σ (w i) * w i = 1} = s n) (n : ℕ)
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h : V →ₛₗ[σ] V →ₗ[K] K)
    (hh : Herm h) (hn : Nondeg h) (hfin : finrank K V = n) :
    Nat.card {v : V // h v v = 1} = s n := by
  obtain ⟨b, hb⟩ := exists_orthonormal hσ n V h hh hn hfin
  rw [← hs n]
  exact Nat.card_congr (Equiv.subtypeEquiv b.equivFun.toEquiv (fun v => by
    rw [form_norm_orthonormal_coords b hb v]; rfl))
end Formalism.FourierDecayAlt.P.S3x6
