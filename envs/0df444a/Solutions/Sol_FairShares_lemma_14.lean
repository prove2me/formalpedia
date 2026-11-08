-- Prove2me | solution 1 for FairShares.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:40:10.998104+00:00
-- url     : https://prove2.me/submissions/01dfdb0b-aa0d-46a1-9842-d9f1db5db215

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_SelfMaxAt

namespace Aux_FairShares_lemma_14
open FairShares

theorem steal {m n : ℕ} (v v' : Finset (Fin m) → ℝ) (k : Fin n) :
    ∀ (ps : List (Fin n)) (R H : Finset (Fin m)),
      ∃ H', v H' ≤ gameVal v k ps R H ∧ gameVal v' k ps R H ≤ v' H' := by
  intro ps
  induction ps with
  | nil => intro R H; exact ⟨H, by simp [gameVal], by simp [gameVal]⟩
  | cons p ps ih =>
    intro R H
    by_cases hR : R.Nonempty
    · by_cases hp : p = k
      · obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup' hR
          (fun e => gameVal v' k ps (R.erase e) (insert e H))
        obtain ⟨H', h1, h2⟩ := ih (R.erase e) (insert e H)
        refine ⟨H', ?_, ?_⟩
        · simp only [gameVal, dif_pos hR, if_pos hp]
          exact h1.trans (Finset.le_sup' (fun e => gameVal v k ps (R.erase e) (insert e H)) he)
        · simp only [gameVal, dif_pos hR, if_pos hp]
          rw [hmax]; exact h2
      · obtain ⟨e, he, hmin⟩ := Finset.exists_mem_eq_inf' hR
          (fun e => gameVal v k ps (R.erase e) H)
        obtain ⟨H', h1, h2⟩ := ih (R.erase e) H
        refine ⟨H', ?_, ?_⟩
        · simp only [gameVal, dif_pos hR, if_neg hp]
          rw [hmin]; exact h1
        · simp only [gameVal, dif_pos hR, if_neg hp]
          exact (Finset.inf'_le (fun e => gameVal v' k ps (R.erase e) H) he).trans h2
    · exact ⟨H, by simp [gameVal, dif_neg hR], by simp [gameVal, dif_neg hR]⟩

end Aux_FairShares_lemma_14

open FairShares Aux_FairShares_lemma_14 in
theorem solution {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n) (D : Set (Finset (Fin m) → ℝ)) :
    SelfMaxAt D (pickShare ω) := by
  intro v _ v' _
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun k => pickValue ω v k)
  obtain ⟨H, h1, h2⟩ := steal v v' k (List.ofFn ω) Finset.univ ∅
  have hv : v H ≤ pickShare ω v := by
    unfold pickShare; rw [← hk]; exact h1
  have hv' : pickShare ω v' ≤ v' H := by
    unfold pickShare
    exact (ciInf_le (Finite.bddBelow_range _) k).trans h2
  unfold shareGuarantee impliedGuarantee
  calc (Finset.univ.filter (fun S : Finset (Fin m) => pickShare ω v' ≤ v' S)).inf
        (fun S => ((v S : ℝ) : WithTop ℝ)) ≤ ((v H : ℝ) : WithTop ℝ) :=
        Finset.inf_le (by simp [hv'])
    _ ≤ _ := by
        apply Finset.le_inf
        intro S hS
        simp only [Finset.mem_filter] at hS
        exact WithTop.coe_le_coe.mpr (hv.trans hS.2)
