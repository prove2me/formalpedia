-- Prove2me | solution 1 for FairShares.pickShare_is_bundle_value
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:36:30.854225+00:00
-- url     : https://prove2.me/submissions/86732f54-8857-410b-abeb-88fa9e0bdd76

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_shareGuarantee

open FairShares in
theorem solution {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n)
    (v : Finset (Fin m) → ℝ) :
    (∃ S : Finset (Fin m), v S = pickShare ω v) ∧
      shareGuarantee (pickShare ω) v = ((pickShare ω v : ℝ) : WithTop ℝ) := by
  have hgame : ∀ (k : Fin n) (ps : List (Fin n)) (R H : Finset (Fin m)),
      ∃ H', gameVal v k ps R H = v H' := by
    intro k ps
    induction ps with
    | nil => intro R H; exact ⟨H, by simp only [gameVal]⟩
    | cons p ps ih =>
      intro R H
      simp only [gameVal]
      by_cases hR : R.Nonempty
      · rw [dif_pos hR]
        by_cases hp : p = k
        · rw [if_pos hp]
          obtain ⟨e, _, heq⟩ := Finset.exists_mem_eq_sup' hR
            (fun e => gameVal v k ps (R.erase e) (insert e H))
          rw [heq]; exact ih _ _
        · rw [if_neg hp]
          obtain ⟨e, _, heq⟩ := Finset.exists_mem_eq_inf' hR
            (fun e => gameVal v k ps (R.erase e) H)
          rw [heq]; exact ih _ _
      · rw [dif_neg hR]
        exact ⟨H, rfl⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k => pickValue ω v k)
  obtain ⟨H', hH'⟩ := hgame k0 (List.ofFn ω) Finset.univ ∅
  have h1 : v H' = pickShare ω v := by
    unfold pickShare
    rw [← hk0]
    unfold pickValue
    exact hH'.symm
  refine ⟨⟨H', h1⟩, ?_⟩
  unfold shareGuarantee impliedGuarantee
  apply le_antisymm
  · have hmem : H' ∈ Finset.univ.filter (fun S : Finset (Fin m) => pickShare ω v ≤ v S) := by
      simp [h1]
    exact (Finset.inf_le (f := fun S => ((v S : ℝ) : WithTop ℝ)) hmem).trans
      (le_of_eq (by rw [h1]))
  · apply Finset.le_inf
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact WithTop.coe_le_coe.mpr hS
