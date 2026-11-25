-- Prove2me | solution 1 for DetDLP.divisor_bisection_and_btn_scale
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:03:17.487049+00:00
-- url     : https://prove2.me/submissions/85ac0bc8-b2b8-4239-b800-b3f91436a6da

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

open DetDLP

private lemma minFac_proper_divisor (N : ℕ) (hN : 2 ≤ N) (hnp : ¬ N.Prime) :
    2 ≤ N.minFac ∧ N.minFac < N ∧ N.minFac ∣ N := by
  have h1 : N ≠ 1 := by omega
  have hprime : N.minFac.Prime := Nat.minFac_prime h1
  have hdvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hle : N.minFac ≤ N := Nat.minFac_le (by omega)
  have hne : N.minFac ≠ N := fun heq => hnp (heq ▸ hprime)
  exact ⟨hprime.two_le, Nat.lt_of_le_of_ne hle hne, hdvd⟩

theorem solution :
    (∀ N : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ N.minFac ∧ N.minFac < N ∧ N.minFac ∣ N) ∧
    (∀ N L M R : ℕ, L ≤ M → M ≤ R →
      ((Finset.Ico L R).filter (fun d => d ∣ N)).card =
        ((Finset.Ico L M).filter (fun d => d ∣ N)).card +
        ((Finset.Ico M R).filter (fun d => d ∣ N)).card) ∧
    (∀ N L M R : ℕ, 2 ≤ N → ¬ N.Prime → 2 ≤ L → L ≤ N.minFac → N.minFac < R → L ≤ M → M ≤ R →
      (N.minFac < M ↔ 0 < ((Finset.Ico L M).filter (fun d => d ∣ N)).card) ∧
      (M ≤ N.minFac ↔ ((Finset.Ico L M).filter (fun d => d ∣ N)).card = 0)) := by
  refine ⟨minFac_proper_divisor, ?_, ?_⟩
  · intro N L M R hLM hMR
    have hunion : Finset.Ico L R = Finset.Ico L M ∪ Finset.Ico M R :=
      (Finset.Ico_union_Ico_eq_Ico hLM hMR).symm
    have hdisj : Disjoint (Finset.Ico L M) (Finset.Ico M R) :=
      Finset.Ico_disjoint_Ico_consecutive L M R
    rw [hunion, Finset.filter_union]
    exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)
  · intro N L M R hN hnp hL2 hLmin hminR _ _
    have hlt_iff : N.minFac < M ↔ 0 < ((Finset.Ico L M).filter (fun d => d ∣ N)).card := by
      constructor
      · intro hlt
        refine Finset.card_pos.mpr ⟨N.minFac, ?_⟩
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hLmin, hlt⟩, Nat.minFac_dvd N⟩
      · intro hpos
        obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_filter, Finset.mem_Ico] at hd
        have hd2 : 0 < d := by omega
        have hd1 : d ≠ 1 := by omega
        have hmin_le : N.minFac ≤ d := Nat.minFac_le_of_dvd (by omega) hd.2
        omega
    refine ⟨hlt_iff, ?_⟩
    rw [← not_lt, hlt_iff]
    omega
