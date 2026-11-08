-- Prove2me | solution 1 for FairShares.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:29:18.275399+00:00
-- url     : https://prove2.me/submissions/f952ce35-7335-4c53-9b6d-ae865ca0186f

import Mathlib
import Definitions.Def_FairShares_pickShare
import Definitions.Def_FairShares_FeasibleAt

namespace Aux_FairShares_l15
open FairShares

def H {m n : ℕ} (A : Fin m → Fin n) (R : Finset (Fin m)) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => j ∉ R ∧ A j = i)

lemma H_empty {m n : ℕ} (A : Fin m → Fin n) (i : Fin n) : H A ∅ i = bundle A i := by
  ext j; simp [H, bundle]

lemma H_univ {m n : ℕ} (A : Fin m → Fin n) (i : Fin n) : H A Finset.univ i = ∅ := by
  ext j; simp [H]

lemma H_step_self {m n : ℕ} (A : Fin m → Fin n) (R : Finset (Fin m)) (e : Fin m) (he : e ∈ R)
    (p : Fin n) : H (Function.update A e p) (R.erase e) p = insert e (H A R p) := by
  ext j
  by_cases hj : j = e
  · subst hj; simp [H]
  · simp [H, Function.update_apply, hj]

lemma H_step_other {m n : ℕ} (A : Fin m → Fin n) (R : Finset (Fin m)) (e : Fin m) (he : e ∈ R)
    (p i : Fin n) (hi : i ≠ p) : H (Function.update A e p) (R.erase e) i = H A R i := by
  ext j
  by_cases hj : j = e
  · subst hj; simp [H, he, Ne.symm hi]
  · simp [H, Function.update_apply, hj]

lemma main {m n : ℕ} (vs : Fin n → (Finset (Fin m) → ℝ)) :
    ∀ (ps : List (Fin n)) (R : Finset (Fin m)) (A : Fin m → Fin n), R.card ≤ ps.length →
      ∃ A' : Fin m → Fin n, ∀ i, gameVal (vs i) i ps R (H A R i) ≤ vs i (bundle A' i) := by
  intro ps
  induction ps with
  | nil =>
    intro R A hR
    have : R = ∅ := Finset.card_eq_zero.1 (by simpa using hR)
    subst this
    refine ⟨A, fun i => ?_⟩
    simp only [gameVal, H_empty, le_refl]
  | cons p ps ih =>
    intro R A hR
    by_cases hne : R.Nonempty
    · obtain ⟨e, he, hemax⟩ := Finset.exists_mem_eq_sup' hne
        (fun e => gameVal (vs p) p ps (R.erase e) (insert e (H A R p)))
      have hc : (R.erase e).card ≤ ps.length := by
        rw [Finset.card_erase_of_mem he]
        simp only [List.length_cons] at hR
        omega
      obtain ⟨A', hA'⟩ := ih (R.erase e) (Function.update A e p) hc
      refine ⟨A', fun i => ?_⟩
      by_cases hip : i = p
      · subst hip
        have := hA' i
        rw [H_step_self A R e he] at this
        simp only [gameVal, dif_pos hne, if_pos rfl]
        rw [hemax]; exact this
      · have := hA' i
        rw [H_step_other A R e he p i hip] at this
        simp only [gameVal, dif_pos hne, if_neg (Ne.symm hip)]
        exact le_trans (Finset.inf'_le _ he) this
    · have : R = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
      subst this
      refine ⟨A, fun i => ?_⟩
      simp only [gameVal, Finset.not_nonempty_empty, dite_false, H_empty, le_refl]

end Aux_FairShares_l15

open FairShares Aux_FairShares_l15 in
theorem solution {m n : ℕ} (hn : 1 ≤ n) (ω : Fin m → Fin n) (D : Set (Finset (Fin m) → ℝ)) :
    FeasibleAt n D (pickShare ω) := by
  intro vs _
  have hlen : (Finset.univ : Finset (Fin m)).card ≤ (List.ofFn ω).length := by simp
  obtain ⟨A', hA'⟩ := main vs (List.ofFn ω) Finset.univ (fun _ => ⟨0, hn⟩) hlen
  refine ⟨A', fun i => ?_⟩
  have h1 : pickShare ω (vs i) ≤ pickValue ω (vs i) i :=
    ciInf_le (Set.finite_range _).bddBelow i
  have h2 := hA' i
  rw [H_univ] at h2
  exact le_trans h1 h2
