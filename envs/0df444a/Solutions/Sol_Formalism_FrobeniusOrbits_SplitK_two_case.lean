-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.two_case
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:24.034798+00:00
-- url     : https://prove2.me/submissions/7aaaa254-aaf4-4ea6-99ad-607e893fd1b2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_bK_sq_int
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_bK_ne_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_exists_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_apply_bK_of_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_ncard_two
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_stab_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd0 : 0 < d) (hd7 : d % 8 = 7) (hb : b ^ 2 = -(d : L)) (p : ℕ) [Fact p.Prime]
    (hp2 : p = 2) (P : Ideal (𝓞 (Kd b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2 := by
  obtain ⟨ι, hι⟩ := exists_ne_one hd0 hb
  apply ncard_two hd0 hb p P ι
  intro heq
  have : P.LiesOver (span {(2 : ℤ)}) := by
    subst hp2
    simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hx : bK b ^ 2 = ((4 * (2 * c) + 1 : ℤ) : Kd b) := by rw [← hc, bK_sq_int hb]
  have hfix := stab_fix (bK b) c hx P ι (MulAction.mem_stabilizer_iff.mpr heq)
  rw [apply_bK_of_ne hd0 hb ι hι] at hfix
  apply bK_ne_zero hd0 hb
  have h2 : (2 : Kd b) * bK b = 0 := by linear_combination -hfix
  simpa using h2
end Formalism.FrobeniusOrbits.SplitK
