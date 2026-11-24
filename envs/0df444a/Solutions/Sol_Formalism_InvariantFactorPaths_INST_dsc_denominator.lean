-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.dsc_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:31.202405+00:00
-- url     : https://prove2.me/submissions/a80dc93d-32b4-46be-b2b2-3dedd2a3a0fb

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSIdxFinite
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRational


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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ g ∈ dualWeyl ℤ r n ν, N • g ∈ weyl ℤ r n hn ν := by
  obtain ⟨b, ⟨_, hspan, _⟩, _⟩ := sSBasis ℤ r n ν
  have : Fintype (ssIdx r n ν) := (sSIdxFinite r n ν).fintype
  have hb : ∀ i, b i ∈ dualWeyl ℤ r n ν := fun i => hspan ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc0 hc using fun i => weylRational r n hn ν hν (b i) (hb i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i, fun g hg => ?_⟩
  rw [← hspan] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i), mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hc i)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
end Formalism.InvariantFactorPaths.INST
