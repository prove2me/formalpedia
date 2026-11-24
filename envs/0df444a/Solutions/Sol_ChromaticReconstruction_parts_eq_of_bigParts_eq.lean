-- Prove2me | solution 1 for ChromaticReconstruction.parts_eq_of_bigParts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:17:43.876898+00:00
-- url     : https://prove2.me/submissions/687ee381-5ea7-49ff-bc50-59b349b9bb4a

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {k : ℕ} {μ ν : Nat.Partition k} (h : bigParts μ = bigParts ν) :
    μ = ν := by
  have hsmall : ∀ ρ : Nat.Partition k, ρ.parts.filter (fun a => ¬ 2 ≤ a) =
      Multiset.replicate (Multiset.card (ρ.parts.filter fun a => ¬ 2 ≤ a)) 1 := by
    intro ρ
    rw [Multiset.eq_replicate]
    refine ⟨rfl, fun b hb => ?_⟩
    rw [Multiset.mem_filter] at hb
    have := ρ.parts_pos hb.1
    omega
  have hsum : ∀ ρ : Nat.Partition k, (bigParts ρ).sum +
      Multiset.card (ρ.parts.filter fun a => ¬ 2 ≤ a) = k := by
    intro ρ
    have := congrArg Multiset.sum (Multiset.filter_add_not (2 ≤ ·) ρ.parts)
    rw [Multiset.sum_add, ρ.parts_sum, hsmall ρ, Multiset.sum_replicate, smul_eq_mul,
      mul_one] at this
    exact this
  apply Nat.Partition.ext
  rw [← Multiset.filter_add_not (2 ≤ ·) μ.parts, ← Multiset.filter_add_not (2 ≤ ·) ν.parts,
    hsmall μ, hsmall ν]
  have e1 := hsum μ
  have e2 := hsum ν
  rw [h] at e1
  change bigParts μ + _ = bigParts ν + _
  rw [h, show Multiset.card (μ.parts.filter fun a => ¬ 2 ≤ a) =
    Multiset.card (ν.parts.filter fun a => ¬ 2 ≤ a) by omega]
end ChromaticReconstruction
