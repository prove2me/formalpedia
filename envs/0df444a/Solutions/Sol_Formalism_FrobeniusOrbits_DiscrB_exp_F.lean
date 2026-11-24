-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.exp_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:45.395651+00:00
-- url     : https://prove2.me/submissions/0d574fd3-53a0-4f21-ab9d-056b5ce03e5d

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
theorem _root_.solution (e : ℕ) : (2 ^ e * (e + 1) - 1) * 2 = 2 ^ (e + 1) * (e + 1) - 2 := by
  rw [Nat.sub_mul, one_mul, show 2 ^ (e + 1) * (e + 1) = 2 ^ e * (e + 1) * 2 by ring]
end Formalism.FrobeniusOrbits.DiscrB
