-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.LemmaU.choose_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:54.467131+00:00
-- url     : https://prove2.me/submissions/e2201165-d2eb-4204-951c-07a689b90129

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
namespace Formalism.DoubleCosetMeasures.P.LemmaU
theorem _root_.solution {J' : Subgroup (GL (Fin a) F)} {y : Matrix (Fin a) (Fin a) F}
    (h : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) (k : J')
    (e : ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) : Classical.choose h = k := by
  have hs := Classical.choose_spec h
  apply Subtype.ext
  apply Units.ext
  exact hs.trans e.symm
end Formalism.DoubleCosetMeasures.P.LemmaU
