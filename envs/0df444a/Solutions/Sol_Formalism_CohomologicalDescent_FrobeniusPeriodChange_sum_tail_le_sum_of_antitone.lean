-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.sum_tail_le_sum_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:47.128213+00:00
-- url     : https://prove2.me/submissions/973ef5bf-0d6b-4a50-8709-f3e9c4cd1072

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution {N : ℕ} (f : Fin N → ℤ) (hf : Antitone f) (m : ℕ) (J : Finset (Fin N))
    (hJ : J.card = (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)), f a ≤ ∑ a ∈ J, f a := by
  set T := Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)) with hT
  rcases Nat.lt_or_ge m N with hmN | hmN
  · set v := f ⟨m, hmN⟩
    have h1 : ∀ x ∈ T \ J, f x ≤ v := by
      intro x hx
      have hx1 : m ≤ (x : ℕ) := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hx).1).2
      exact hf (show (⟨m, hmN⟩ : Fin N) ≤ x from hx1)
    have h2 : ∀ x ∈ J \ T, v ≤ f x := by
      intro x hx
      have hx2 : ¬ m ≤ (x : ℕ) := fun h =>
        (Finset.mem_sdiff.1 hx).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      exact hf (show x ≤ (⟨m, hmN⟩ : Fin N) from by show (x : ℕ) ≤ m; omega)
    have hc : (T \ J).card = (J \ T).card := by
      have e1 := Finset.card_sdiff_add_card_inter T J
      have e2 := Finset.card_sdiff_add_card_inter J T
      rw [Finset.inter_comm] at e2
      omega
    have s1 := Finset.sum_le_card_nsmul (T \ J) f v h1
    have s2 := Finset.card_nsmul_le_sum (J \ T) f v h2
    rw [hc] at s1
    rw [nsmul_eq_mul] at s1 s2
    have split : ∀ S U : Finset (Fin N), ∑ x ∈ S \ U, f x + ∑ x ∈ S ∩ U, f x = ∑ x ∈ S, f x := by
      intro S U
      first
      | exact Finset.sum_sdiff_add_sum_inter S U f
      | (rw [add_comm]; exact Finset.sum_inter_add_sum_diff S U f)
      | (rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S U), Finset.sdiff_union_inter])
    have e3 := split T J
    have e4 := split J T
    rw [Finset.inter_comm] at e4
    linarith
  · have hT0 : T = ∅ := Finset.filter_eq_empty_iff.2 (fun x _ => by have := x.2; omega)
    have hJ0 : J = ∅ := Finset.card_eq_zero.1 (by rw [hJ, hT0, Finset.card_empty])
    rw [hT0, hJ0]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
