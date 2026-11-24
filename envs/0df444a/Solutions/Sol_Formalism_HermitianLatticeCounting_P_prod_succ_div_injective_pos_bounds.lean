-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prod_succ_div_injective_pos_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:22.355618+00:00
-- url     : https://prove2.me/submissions/732899aa-48ba-49da-9b95-f2de8f6d32f0

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_succ_div_nat_le_card_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} (I : Finset ι) (y : ι → ℕ) (hinj : Set.InjOn y (I : Set ι)) (h1 : ∀ i ∈ I, 1 ≤ y i) :
    1 ≤ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) ∧ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) ≤ (I.card : ℝ) + 1 := by
  have himg : ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) = ∏ t ∈ I.image y, (((t : ℝ) + 1) / (t : ℝ)) :=
    by rw [Finset.prod_image (fun a ha b hb h => hinj ha hb h)]
  have hcard : (I.image y).card = I.card := Finset.card_image_of_injOn hinj
  constructor
  · calc (1:ℝ) = ∏ i ∈ I, (1:ℝ) := by simp
      _ ≤ ∏ i ∈ I, (((y i : ℝ) + 1) / (y i : ℝ)) := by
          refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i hi => ?_)
          have hy : (0:ℝ) < y i := by exact_mod_cast h1 i hi
          rw [le_div_iff₀ hy]
          linarith
  · rw [himg]
    have := prod_succ_div_nat_le_card_succ (I.image y) (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      exact h1 i hi)
    rw [hcard] at this
    exact this
end Formalism.HermitianLatticeCounting.P
