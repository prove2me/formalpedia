-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.sqF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:46.894903+00:00
-- url     : https://prove2.me/submissions/f3a27789-7c4b-4703-b625-06950cdd2793

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
variable {e q d : ℕ} {ζ a b : L}
namespace Formalism.FrobeniusOrbits.DiscrB
theorem _root_.solution (e q d : ℕ) :
    ((2 : ℤ) ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e)) ^ 2 =
      (2 : ℤ) ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) := by
  have hB : 2 ^ (e + 2) * (e + 1) - 4 = (2 ^ (e + 1) * (e + 1) - 2) * 2 := by
    rw [Nat.sub_mul, show 2 ^ (e + 2) * (e + 1) = 2 ^ (e + 1) * (e + 1) * 2 by ring]
  rw [hB, mul_pow, ← pow_mul, ← pow_mul, ← pow_succ]
end Formalism.FrobeniusOrbits.DiscrB
