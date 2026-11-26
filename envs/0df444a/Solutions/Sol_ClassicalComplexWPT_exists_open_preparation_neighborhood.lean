-- Prove2me | solution 1 for ClassicalComplexWPT.exists_open_preparation_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:52.713721+00:00
-- url     : https://prove2.me/submissions/85d1d3b7-075c-4389-a4b6-91e7fcffc968

import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Definitions.Def_ClassicalComplexWPT_Main
import Theorems.Thm_ClassicalComplexWPT_exists_isWeierstrassPreparation


set_option autoImplicit true
open Filter
open scoped BigOperators Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution
    (n d : ℕ) (f : Ambient n → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ) (s : Set (Ambient n)),
      IsWeierstrassPreparation f d a u ∧
      IsOpen s ∧ (0 : Ambient n) ∈ s ∧
      (∀ x ∈ s, u x ≠ 0) ∧
      ∀ x ∈ s, f x = u x * preparedPolynomial d a x := by
  obtain ⟨a, u, hprep⟩ := exists_isWeierstrassPreparation hf horder
  have hunit : ∀ᶠ x : Ambient n in 𝓝 0, u x ≠ 0 :=
    hprep.2.2.1.continuousAt.eventually_ne hprep.2.2.2.1
  have hfactor : ∀ᶠ x : Ambient n in 𝓝 0,
      f x = u x * preparedPolynomial d a x := hprep.2.2.2.2
  obtain ⟨s, hs, hsOpen, hs0⟩ := mem_nhds_iff.mp (hunit.and hfactor)
  refine ⟨a, u, s, hprep, hsOpen, hs0, ?_, ?_⟩
  · intro x hx
    exact (hs hx).1
  · intro x hx
    exact (hs hx).2
end ClassicalComplexWPT
