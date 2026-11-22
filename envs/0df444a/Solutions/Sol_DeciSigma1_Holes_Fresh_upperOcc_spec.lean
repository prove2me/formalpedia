-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.upperOcc_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:04.935846+00:00
-- url     : https://prove2.me/submissions/752e7455-20e5-4717-a5b2-daf24e0d2a74

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_previousAnchor
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_bounds
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_succ_subset


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    o.2.1 < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧ o.2.2 ∈ anchors W t o.1 ∧
      (o.2.1 = 0 ∨ o.2.1 ∈ anchors W t o.1) ∧
      ∀ p ∈ anchors W (t + 1) o.1, ¬ (o.2.1 < p ∧ p < o.2.2) := by
  obtain ⟨hl, he, hs⟩ := mem_upperOcc.mp ho
  obtain ⟨he1, he2⟩ := anchors_bounds hl he
  have hsub := anchors_succ_subset (W := W) t o.1
  rw [hs]
  refine ⟨?_, he2, hsub he, ?_, ?_⟩
  · by_cases hex : ∃ q ∈ anchors W (t + 1) o.1, q < o.2.2
    · exact (previousAnchor_spec hex).2
    · have : upperOccurrenceStart W t o.1 o.2.2 ≤ 0 :=
        previousAnchor_le (fun q hq hqe => absurd ⟨q, hq, hqe⟩ hex)
      omega
  · by_cases hex : ∃ q ∈ anchors W (t + 1) o.1, q < o.2.2
    · exact Or.inr (hsub (previousAnchor_spec hex).1)
    · left
      have : upperOccurrenceStart W t o.1 o.2.2 ≤ 0 :=
          previousAnchor_le (fun q hq hqe => absurd ⟨q, hq, hqe⟩ hex)
      omega
  · rintro p hp ⟨h1, h2⟩
    have := le_previousAnchor hp h2
    unfold upperOccurrenceStart at h1
    omega
end DeciSigma1.Holes.Fresh
