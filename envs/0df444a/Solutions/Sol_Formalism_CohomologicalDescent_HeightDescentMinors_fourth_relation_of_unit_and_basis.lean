-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.fourth_relation_of_unit_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:32.542996+00:00
-- url     : https://prove2.me/submissions/d90b2af8-29a3-46c8-84c8-39a64973dc1c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_pi0Subst_mul
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_inc_X_sub_l_eq_q0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (h3 : UnitFactorQ) (hb : PowerSeriesFreeBasis) : R4 := by
  intro l _ O _ _ h2 S m y hm
  obtain ⟨g, hg, -⟩ := h3 l O h2
  have hpos := prime_sub_one_pos_alt l
  have hq : q l O = ((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * q0 l O := by
    rw [hg, Units.inv_mul_cancel_left]
  obtain ⟨a, ha, -⟩ := hb l O h2 (((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) ^ S * y)
  have ha' : ((g⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) ^ S * y =
      ∑ j : Fin (l - 1), inc l O (a j) * X ^ (j : ℕ) := ha
  obtain ⟨a0, -, huniq⟩ := hb l O h2 (inc l O m)
  have e1 : inc l O m =
      ∑ j : Fin (l - 1), inc l O ((X - C (l : O)) ^ S * a j) * X ^ (j : ℕ) := by
    have hj : ∀ j : Fin (l - 1), inc l O ((X - C (l : O)) ^ S * a j) * X ^ (j : ℕ) =
        q0 l O ^ S * (inc l O (a j) * X ^ (j : ℕ)) := by
      intro j
      rw [pi0Subst_mul, inc_pow, inc_X_sub_l_eq_q0]
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum, ← ha', hm, hq]
    ring
  have e2 : inc l O m =
      ∑ j : Fin (l - 1), inc l O (if (j : ℕ) = 0 then m else 0) * X ^ (j : ℕ) := by
    rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (l - 1))]
    · simp
    · intro b _ hb'
      rw [if_neg (fun h => hb' (Fin.ext h)), inc_zero, zero_mul]
    · simp
  have e3 := (huniq _ e1).trans (huniq _ e2).symm
  have e4 := congrFun e3 ⟨0, hpos⟩
  exact ⟨a ⟨0, hpos⟩, by simpa using e4.symm⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
