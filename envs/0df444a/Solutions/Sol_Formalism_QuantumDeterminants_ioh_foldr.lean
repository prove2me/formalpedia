-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:46.343675+00:00
-- url     : https://prove2.me/submissions/1a4db000-0788-46e2-920c-f3076db6f259

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_QP
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_Top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) (l : List (ℂ × Fin n × Fin n))
    (G : Matrix (Fin n) (Fin n) ℂ → E) :
    (l.map fun p => Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) G =
      fun x => (l.map fun p => Top (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) p.1 p.2.1 p.2.2).foldr
        (fun T h => T h) (fun y => G (Q * y * P)) (P * x * Q) := by
  induction l with
  | nil =>
    funext x
    simp only [List.map_nil, List.foldr_nil, ioh_QP P Q x hQP]
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, ioh_Top ε H P Q hQP hPQ hH]
end Formalism.QuantumDeterminants
