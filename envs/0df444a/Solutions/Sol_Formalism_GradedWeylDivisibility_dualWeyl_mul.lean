-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.dualWeyl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:13.919509+00:00
-- url     : https://prove2.me/submissions/6afffc1a-52d8-4a4f-8986-a84c894679ae

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_mem_dualWeyl_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n : ℕ} {ν μ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ dualWeyl R r n ν) (hg : g ∈ dualWeyl R r n μ) :
    f * g ∈ dualWeyl R r n (ν + μ) := by
  rw [mem_dualWeyl_iff] at *
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]
end Formalism.GradedWeylDivisibility
