-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.odd_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:22:18.515217+00:00
-- url     : https://prove2.me/submissions/042c218f-f677-4757-9653-4d0e67e0bf08

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.DiscrB
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.DiscrB
theorem _root_.solution {q : ℕ} (h : q % 2 = 1) : Odd (q : ℤ) :=
  ⟨((q / 2 : ℕ) : ℤ), by have := Nat.div_add_mod q 2; omega⟩
end Formalism.FrobeniusOrbits.DiscrB
