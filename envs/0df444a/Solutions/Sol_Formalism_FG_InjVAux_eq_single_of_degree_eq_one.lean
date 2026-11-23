-- Prove2me | solution 1 for Formalism.FG.InjVAux.eq_single_of_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:21.165914+00:00
-- url     : https://prove2.me/submissions/056a9629-e684-45fa-9522-3fafaa160768

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
namespace Formalism.FG.InjVAux
theorem _root_.solution {ι : Type*} [Fintype ι] (e : ι →₀ ℕ)
    (he : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  rw [Finsupp.degree_eq_sum] at he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    rw [Finset.sum_eq_zero (fun k _ => hc k)] at he
    exact zero_ne_one he
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => e k) (Finset.mem_univ i)
  rw [he] at hsplit
  have hei : e i = 1 := by omega
  refine ⟨i, ?_⟩
  ext k
  by_cases hk : k = i
  · subst hk; simp [hei]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hk)]
    have : e k ≤ ∑ x ∈ Finset.univ.erase i, e x :=
      Finset.single_le_sum (f := fun x => e x) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    omega
end Formalism.FG.InjVAux
