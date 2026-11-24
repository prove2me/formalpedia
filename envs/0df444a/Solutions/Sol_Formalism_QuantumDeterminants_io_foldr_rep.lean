-- Prove2me | solution 1 for Formalism.QuantumDeterminants.io_foldr_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:09.154386+00:00
-- url     : https://prove2.me/submissions/89fcfad5-a462-42df-b4f0-33d3d509c90b

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_io_Tm_rep

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
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.foldr_nil, List.prod_nil, Module.End.one_apply]
    exact h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact io_Tm_rep ih _ _ _
end Formalism.QuantumDeterminants
