-- Prove2me | solution 1 for EdenVerified.D05_actual_forward_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:43.239256+00:00
-- url     : https://prove2.me/submissions/211c9c6f-f003-408a-9d9f-269ae9bc3274

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_contDiff_evolution
import Theorems.Thm_Eden_evolution_add
import Theorems.Thm_Eden_evolution_unique
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_evolution
attribute [local simp] Eden.evolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) :
    (∀ p : PhaseSpace, evolution c 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => evolution c τ p)
        (vectorField c (evolution c t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => evolution c t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      evolution c (s + t) p = evolution c t (evolution c s p)) ∧
    (∀ (t : ℝ), 0 ≤ t → ∀ n : WithTop ℕ∞, ContDiff ℝ n (evolution c t)) := by
  exact ⟨fun p => ⟨evolution_zero_time c p, fun _ ht => hasDerivAt_evolution c ht p⟩,
    fun p f hf hf' h0 => evolution_unique c p hf hf' h0,
    fun s t hs ht p => evolution_add c hs ht p,
    fun t ht n => contDiff_evolution c ht n⟩
end EdenVerified
