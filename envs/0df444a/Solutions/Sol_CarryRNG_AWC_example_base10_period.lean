-- Prove2me | solution 1 for CarryRNG.AWC.example_base10_period
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:10:40.58876+00:00
-- url     : https://prove2.me/submissions/e0a5ee65-337e-49bc-8f7c-34c1c8d8ac67

import Mathlib
import Definitions.Def_CarryRNG_AWC_step
import Definitions.Def_CarryRNG_AWC_zeroSeed
import Definitions.Def_CarryRNG_AWC_topSeed

set_option autoImplicit false

namespace CarryRNG.AWC

abbrev L10 : Lags := ⟨2, 1, by norm_num, by norm_num⟩

/-- componentwise equality of states (the derived `DecidableEq` does not reduce in the kernel) -/
def Peq {b r : ℕ} (z w : State b r) : Prop := (∀ i, z.x i = w.x i) ∧ z.c = w.c

instance {b r : ℕ} (z w : State b r) : Decidable (Peq z w) :=
  inferInstanceAs (Decidable ((∀ i, z.x i = w.x i) ∧ z.c = w.c))

lemma Peq_iff {b r : ℕ} (z w : State b r) : Peq z w ↔ z = w := by
  constructor
  · rintro ⟨h1, h2⟩
    cases z; cases w
    simp only at h1 h2
    congr
    · exact funext h1
  · rintro rfl; exact ⟨fun _ => rfl, rfl⟩

lemma chk_good : ∀ z : State 10 L10.r,
    ((z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0)) →
    (Peq ((step 10 L10)^[108] z) z ∧ ¬ Peq ((step 10 L10)^[54] z) z ∧
      ¬ Peq ((step 10 L10)^[36] z) z) := by decide +kernel

lemma chk_rest : ∀ z : State 10 L10.r,
    ¬ ((z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0)) →
    ¬ Peq z (zeroSeed 10 L10.r (by norm_num)) → ¬ Peq z (topSeed 10 L10.r (by norm_num)) →
    (Peq ((step 10 L10)^[108] (step 10 L10 z)) (step 10 L10 z) ∧
      ¬ Peq ((step 10 L10)^[54] (step 10 L10 z)) (step 10 L10 z) ∧
      ¬ Peq ((step 10 L10)^[36] (step 10 L10 z)) (step 10 L10 z)) := by decide +kernel

lemma minper_108 {α : Type} (f : α → α) (w : α) (h1 : f^[108] w = w) (h2 : f^[54] w ≠ w)
    (h3 : f^[36] w ≠ w) : Function.minimalPeriod f w = 108 := by
  have hp : Function.IsPeriodicPt f 108 w := h1
  have hd : Function.minimalPeriod f w ∣ 108 := hp.minimalPeriod_dvd
  by_contra hne
  have key : ∀ k ∈ Nat.divisors 108, k ≠ 108 → k ∣ 54 ∨ k ∣ 36 := by decide
  rcases key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) hne with h | h
  · exact h2 ((Function.isPeriodicPt_minimalPeriod f w).trans_dvd h)
  · exact h3 ((Function.isPeriodicPt_minimalPeriod f w).trans_dvd h)

theorem example_base10_period' :
    let L : Lags := ⟨2, 1, by norm_num, by norm_num⟩
    (∀ z : State 10 L.r,
        (z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0) →
        Function.minimalPeriod (step 10 L) z = 108) ∧
    (∀ z : State 10 L.r,
        ¬ ((z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0)) →
        z ≠ zeroSeed 10 L.r (by norm_num) → z ≠ topSeed 10 L.r (by norm_num) →
        Function.minimalPeriod (step 10 L) (step 10 L z) = 108) := by
  intro L
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨h1, h2, h3⟩ := chk_good z hz
    exact minper_108 _ z ((Peq_iff _ _).1 h1) (fun h => h2 ((Peq_iff _ _).2 h))
      (fun h => h3 ((Peq_iff _ _).2 h))
  · intro z hz hz0 hzt
    obtain ⟨h1, h2, h3⟩ := chk_rest z hz (fun h => hz0 ((Peq_iff _ _).1 h)) (fun h => hzt ((Peq_iff _ _).1 h))
    exact minper_108 _ _ ((Peq_iff _ _).1 h1) (fun h => h2 ((Peq_iff _ _).2 h))
      (fun h => h3 ((Peq_iff _ _).2 h))

end CarryRNG.AWC

theorem solution :
    let L : CarryRNG.AWC.Lags := ⟨2, 1, by norm_num, by norm_num⟩
    (∀ z : CarryRNG.AWC.State 10 L.r,
        (z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0) →
        Function.minimalPeriod (CarryRNG.AWC.step 10 L) z = 108) ∧
    (∀ z : CarryRNG.AWC.State 10 L.r,
        ¬ ((z.c = 0 ∧ z.x 0 < z.x 1) ∨ (z.c = 1 ∧ z.x 1 < z.x 0)) →
        z ≠ CarryRNG.AWC.zeroSeed 10 L.r (by norm_num) → z ≠ CarryRNG.AWC.topSeed 10 L.r (by norm_num) →
        Function.minimalPeriod (CarryRNG.AWC.step 10 L) (CarryRNG.AWC.step 10 L z) = 108) :=
  CarryRNG.AWC.example_base10_period'
