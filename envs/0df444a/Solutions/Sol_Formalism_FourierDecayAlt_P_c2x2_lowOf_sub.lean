-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x2_lowOf_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:25:56.056465+00:00
-- url     : https://prove2.me/submissions/8abc033c-a95b-4ec8-9620-a95e7a5c5203

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m : ℕ} (p : Fin m × Fin m → Prop) [DecidablePred p] (v : {q : Fin m × Fin m // p q} → ℂ)
    (i j : Fin m) :
    C2.lowOf (fun q : {q : Fin m × Fin m // p q} => q.1) v i j =
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : p (i, j) then v ⟨(i, j), h⟩ else 0 := by
  simp only [C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro e; apply hq; exact Subtype.ext e
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro e; apply h; rw [← e]; exact q.2
end Formalism.FourierDecayAlt.P
