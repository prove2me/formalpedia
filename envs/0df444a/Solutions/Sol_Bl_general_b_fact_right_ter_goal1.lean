-- Prove2me | solution 1 for Bl.general_b_fact_right_ter.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:09.063053+00:00
-- url     : https://prove2.me/submissions/eca72f2d-2c0d-4959-a27d-4bd42852216c

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightTer_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct NumberField IsDedekindDomain
open Bl Bl.general_b_fact_right_ter
namespace Bl.general_b_fact_right_ter
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} (s : Finset ι)
    (Q : ι → 𝓞 F → Prop) (hQ : ∀ i c r, Q i c → Q i (c * r)) (h : ∀ i ∈ s, ∃ c, c ≠ 0 ∧ Q i c) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i ∈ s, Q i c := by
  classical
  choose! c hc0 hcQ using h
  refine ⟨∏ i ∈ s, c i, Finset.prod_ne_zero_iff.mpr hc0, ?_⟩
  intro i hi
  rw [← Finset.mul_prod_erase s c hi]
  exact hQ i _ _ (hcQ i hi)
end Bl.general_b_fact_right_ter
