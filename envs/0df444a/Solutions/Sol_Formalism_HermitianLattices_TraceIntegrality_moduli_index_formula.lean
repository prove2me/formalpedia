-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.moduli_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:46.854509+00:00
-- url     : https://prove2.me/submissions/79de820d-4809-4e6c-9d0e-0b781bbcb826

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentFromBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : Ms_index := by
  intro f N y R2 hf h0 hs
  have hy : ∀ c τ, y c τ ≤ R2 := fun c τ =>
    le_trans (Finset.single_le_sum (fun i _ => h0 c i) (Finset.mem_univ τ)) (hs c)
  have hP : ∏ τ, ∏ c, y c τ ≤ ∏ _τ : Fin f, ∏ _c : Fin N, R2 :=
    Finset.prod_le_prod (fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ)
      (fun τ _ => Finset.prod_le_prod (fun c _ => h0 c τ) (fun c _ => hy c τ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hP
  have hP0 : 0 ≤ ∏ τ, ∏ c, y c τ := Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ
  calc (∏ τ, ∏ c, y c τ) ^ 2 ≤ ((R2 ^ N) ^ f) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    _ = R2 ^ (2 * f * N) := by rw [← pow_mul, ← pow_mul]; ring_nf
end Formalism.HermitianLattices.TraceIntegrality
