-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.exists_minimal_bag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:35:31.645446+00:00
-- url     : https://prove2.me/submissions/f526119c-1a8e-4d4c-ba9b-daa481d498fc

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (T : Finset (Fin n)) (s : ℝ) : ∀ B : Finset G,
    (∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) B) →
    ∃ B' ⊆ B, (∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) B') ∧
      (∀ e ∈ B', ∀ k ∈ T, netSum n (v k) p (t k) (B' \ {e}) < t k / n - s) := by
  intro B
  induction B using Finset.strongInduction with
  | _ B ih =>
    intro hB
    by_cases hex : ∃ e ∈ B, ∃ k ∈ T, t k / n - s ≤ netSum n (v k) p (t k) (B \ {e})
    · obtain ⟨e, he, hk⟩ := hex
      obtain ⟨B', hB'sub, h1, h2⟩ :=
        ih (B \ {e}) (Finset.sdiff_ssubset (by simpa using he) ⟨e, by simp⟩) hk
      exact ⟨B', hB'sub.trans Finset.sdiff_subset, h1, h2⟩
    · push_neg at hex
      exact ⟨B, Finset.Subset.refl _, hB, fun e he k hk => hex e he k hk⟩
end FairSelling.EqualProceedsBagFilling
