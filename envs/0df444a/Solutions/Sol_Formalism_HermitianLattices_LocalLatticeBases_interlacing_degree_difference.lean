-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.interlacing_degree_difference
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:45.5222+00:00
-- url     : https://prove2.me/submissions/89cc4d85-4bba-47de-a9c5-9285a9b16f18

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
theorem _root_.solution : InterlacingDegreeDifference := by
  intro n lam sg h
  have e1 : ∑ i, lam i - ∑ i, sg i = lam 0 + ∑ i : Fin n, (lam i.succ - sg i) := by
    rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]; ring
  have e2 : ∑ i, lam i - ∑ i, sg i = lam (Fin.last n) + ∑ i : Fin n, (lam i.castSucc - sg i) := by
    rw [Fin.sum_univ_castSucc, Finset.sum_sub_distrib]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    have : ∑ i : Fin n, (lam i.succ - sg i) ≤ 0 := Finset.sum_nonpos (fun i _ => by linarith [(h i).2])
    linarith
  · rw [e2]
    have : 0 ≤ ∑ i : Fin n, (lam i.castSucc - sg i) := Finset.sum_nonneg (fun i _ => by linarith [(h i).1])
    linarith
  · intro hn W h1 h2
    rw [e2]
    have : lam (Fin.castSucc ⟨0,hn⟩) - sg ⟨0,hn⟩ ≤ ∑ i : Fin n, (lam i.castSucc - sg i) :=
      Finset.single_le_sum (f := fun i : Fin n => lam i.castSucc - sg i) (fun i _ => by linarith [(h i).1]) (Finset.mem_univ _)
    have h0 : (Fin.castSucc ⟨0,hn⟩ : Fin (n+1)) = 0 := rfl
    rw [h0] at this
    linarith
end Formalism.HermitianLattices.LocalLatticeBases
