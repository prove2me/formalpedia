-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hcl_eq_hcl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:06.788634+00:00
-- url     : https://prove2.me/submissions/d74e0244-947b-45df-bfa9-8248f24d4e9b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
variable {e : ℕ}
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (u v : (ZMod (2 ^ (e + 2)))ˣ) :
    hcl e u = hcl e v ↔ u = v ∨ u = -v := by
  unfold hcl
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases Int.even_or_odd k with hk2 | hk2
    · left
      rw [hk2.neg_one_zpow] at hk
      exact inv_mul_eq_one.mp hk.symm
    · right
      rw [hk2.neg_one_zpow] at hk
      have hv : v = u * -1 := inv_mul_eq_iff_eq_mul.mp hk.symm
      rw [hv, mul_neg_one, neg_neg]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
end Formalism.FrobeniusOrbits
