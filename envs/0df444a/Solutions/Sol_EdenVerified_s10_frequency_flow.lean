-- Prove2me | solution 1 for EdenVerified.s10_frequency_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:01.662715+00:00
-- url     : https://prove2.me/submissions/287ebba2-5f5d-4330-95e8-da296c8d15fc

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_contDiff_frequencyEvolution
import Theorems.Thm_Eden_frequencyEvolution_add
import Theorems.Thm_Eden_frequencyEvolution_sqrt_two
import Theorems.Thm_Eden_frequencyEvolution_unique
import Theorems.Thm_Eden_frequencyEvolution_zero_time
import Theorems.Thm_Eden_frequencyVectorField_sqrt_two
import Theorems.Thm_Eden_hasDerivAt_frequencyEvolution
attribute [local simp] Eden.frequencyEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c ν : ℝ) :
    (∀ p : PhaseSpace, frequencyEvolution c ν 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => frequencyEvolution c ν τ p)
        (frequencyVectorField c ν (frequencyEvolution c ν t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace), ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f
        (frequencyVectorField c ν (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => frequencyEvolution c ν t p) (Ici 0)) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      frequencyEvolution c ν (s+t) p = frequencyEvolution c ν t (frequencyEvolution c ν s p)) ∧
    (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (frequencyEvolution c ν t)) ∧
    frequencyVectorField c (Real.sqrt 2) = vectorField c ∧
    (∀ t : ℝ, frequencyEvolution c (Real.sqrt 2) t = evolution c t) :=
  ⟨fun p => ⟨frequencyEvolution_zero_time c ν p,
      fun t ht => hasDerivAt_frequencyEvolution c ν ht p⟩,
    fun p f hf hf' h0 => frequencyEvolution_unique c ν p hf hf' h0,
    fun s t hs ht p => frequencyEvolution_add c ν hs ht p,
    fun t ht => contDiff_frequencyEvolution c ν ht 1,
    frequencyVectorField_sqrt_two c, frequencyEvolution_sqrt_two c⟩
end EdenVerified
