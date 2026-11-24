-- Prove2me | solution 1 for Formalism.BasicNotions.HNeZero.ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:56.956812+00:00
-- url     : https://prove2.me/submissions/f04efaa4-2eee-4977-b7c6-a219c3f3c1c0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_LocalRingCardinality_DataHost

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
open Formalism Formalism.BasicNotions
namespace Formalism.BasicNotions
namespace HNeZero
theorem _root_.solution {R : Ranks} {H : Host R} {p : ℕ} (h : HNeZero H p) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) : (H.galE σ).2 ≠ 1 := by
  intro h1
  have := h P σ hσ
  rw [h1, orderOf_one] at this
  exact Nat.not_even_one this
end HNeZero
end Formalism.BasicNotions
