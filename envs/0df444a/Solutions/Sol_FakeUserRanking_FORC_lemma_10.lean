-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_10
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:44:55.717749+00:00
-- url     : https://prove2.me/submissions/174561b3-36b7-4a94-8347-5f06dbbc930a

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

open FakeUserRanking.FORC

open Classical in
theorem solution : ¬ (∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        (F : ℝ) + 1 / (n : ℝ) ^ 2 +
          expect inst P (forc n T tb fb) T
            (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
              ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
                ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i)) := by
  rintro ⟨C, hC⟩
  let inst : Instance 1 := ⟨fun _ => 0, fun _ => by simp, fun _ => 0, fun _ => by simp⟩
  have hI : ∀ j : Fin 1, Finset.Ioi j = ∅ := by decide
  have h := hC 1 2 0 le_rfl le_rfl inst (fun a b hab => absurd hab (by omega))
    (fun _ => PMF.pure none) (fun _ _ => rfl) (fun _ _ _ => 0)
    (fun _ _ S hS => by obtain ⟨x, hx⟩ := hS; rwa [Subsingleton.elim (0 : Fin 1) x])
    (fun _ _ => 1)
  simp [hI, expect] at h
  norm_num at h
