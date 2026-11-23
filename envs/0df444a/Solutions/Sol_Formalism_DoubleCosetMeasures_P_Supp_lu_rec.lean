-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.lu_rec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:54.683965+00:00
-- url     : https://prove2.me/submissions/4a758f99-dca9-421a-ada2-8ca3863d82e1

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_exists_continuous_lowerUpper_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
variable {K : Type} [CommRing K] {n : ℕ}
variable [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution : ∃ Ph Pu : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K,
    Continuous Ph ∧ Continuous Pu ∧
      ∀ h u, IsLowUni h → IsUpUni u → Ph (h * u) = h ∧ Pu (h * u) = u := by
  obtain ⟨E, hEc, hE⟩ := exists_continuous_lowerUpper_entry (K := K) (n := n) n
  refine ⟨fun M i j => if j < i then E i j M else if i = j then 1 else 0,
    fun M i j => if i < j then E i j M else if i = j then 1 else 0, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h1 : j < i
    · simp only [h1, if_true]; exact hEc i j
    · simp only [h1, if_false]; exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h1 : i < j
    · simp only [h1, if_true]; exact hEc i j
    · simp only [h1, if_false]; exact continuous_const
  · intro h u hh hu
    have hL : ∀ a b : Fin n, a < b → h a b = 0 := fun a b hab => hh.1 (OrderDual.toDual_lt_toDual.mpr hab)
    have hU : ∀ a b : Fin n, b < a → u a b = 0 := fun a b hab => hu.1 hab
    have hall : ∀ i j, E i j (h * u) = (h + u - 1) i j := fun i j => hE i j (min i j).isLt h u hh hu
    constructor
    · ext i j
      simp only [hall, Matrix.sub_apply, Matrix.add_apply]
      split_ifs with h1 h2
      · rw [hU i j h1, Matrix.one_apply_ne h1.ne']; ring
      · subst h2; rw [hh.2]
      · rw [hL i j (lt_of_le_of_ne (not_lt.mp h1) h2)]
    · ext i j
      simp only [hall, Matrix.sub_apply, Matrix.add_apply]
      split_ifs with h1 h2
      · rw [hL i j h1, Matrix.one_apply_ne h1.ne]; ring
      · subst h2; rw [hu.2]
      · rw [hU i j (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))]
end Formalism.DoubleCosetMeasures.P.Supp
