-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.lpa_joint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:44.349357+00:00
-- url     : https://prove2.me/submissions/30f86a83-ebf3-473b-93a5-ac2e96f73914

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightDominantHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution {K N ι : Type*} [Field K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : ι → Module.End K N) (hcomm : ∀ i j, Commute (f i) (f j))
    (hdiag : ∀ i, ⨆ μ : K, Module.End.eigenspace (f i) μ = ⊤) (s : Finset ι) (C : Submodule K N)
    (hC : ∀ i, ∀ x ∈ C, f i x ∈ C) (hne : C ≠ ⊥) :
    ∃ C' : Submodule K N, C' ≤ C ∧ C' ≠ ⊥ ∧ (∀ i, ∀ x ∈ C', f i x ∈ C') ∧ ∃ μ : ι → K, ∀ i ∈ s, ∀ x ∈ C', f i x = μ i • x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, hne, hC, 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨C', hC'C, hC'ne, hC'st, μ, hμ⟩ := ih
    have key : C' ⊓ ⨆ c, (f i).genEigenspace c 1 = ⨆ c, C' ⊓ (f i).genEigenspace c 1 :=
      Submodule.inf_iSup_genEigenspace (p := C') (f := f i) (fun x hx => hC'st i x hx) 1
    have htop : (⨆ c, (f i).genEigenspace c 1) = ⊤ := hdiag i
    rw [htop, inf_top_eq] at key
    have hex : ∃ c, C' ⊓ (f i).genEigenspace c 1 ≠ ⊥ := by
      by_contra h
      push Not at h
      apply hC'ne
      rw [key]
      exact iSup_eq_bot.mpr h
    obtain ⟨c, hc⟩ := hex
    refine ⟨C' ⊓ (f i).genEigenspace c 1, inf_le_left.trans hC'C, hc, ?_, Function.update μ i c, ?_⟩
    · intro j x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr
        ⟨hC'st j x hx1, Module.End.mapsTo_genEigenspace_of_comm (hcomm i j) c 1 hx2⟩
    · intro j hj x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      rcases Finset.mem_insert.mp hj with hji | hjs
      · rw [hji, Function.update_self]
        exact Module.End.mem_genEigenspace_one.mp hx2
      · have hji : j ≠ i := fun h => hi (h ▸ hjs)
        rw [Function.update_of_ne hji]
        exact hμ j hjs x hx1
end Formalism.CohomologicalDescent.LP
