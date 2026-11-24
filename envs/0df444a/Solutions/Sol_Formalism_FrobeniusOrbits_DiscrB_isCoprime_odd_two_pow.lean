-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.isCoprime_odd_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:45:40.517808+00:00
-- url     : https://prove2.me/submissions/4d215cf1-34a2-40f7-a10f-294a85a4ee0d

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
theorem _root_.solution {m : ℤ} (hm : Odd m) (k : ℕ) : IsCoprime m (2 ^ k) := by
  obtain ⟨j, rfl⟩ := hm
  exact IsCoprime.pow_right ⟨1, -j, by ring⟩
end Formalism.FrobeniusOrbits.DiscrB
