-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.expBounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:07:19.770145+00:00
-- url     : https://prove2.me/submissions/b9fad37b-a4a8-447a-a5a3-76fcf3d6ce01

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_val_split
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : ExpBounded := by
  intro l r ν hl hν
  obtain ⟨b, ⟨_, hspan, _⟩, _⟩ := sSBasis ℤ r r ν
  have hfin : (ssIdx r r ν).Finite := sSIdxFinite r r ν
  have : Fintype (ssIdx r r ν) := hfin.fintype
  have hb : ∀ m : ssIdx r r ν, ∃ c : ℤ, c ≠ 0 ∧ c • b m ∈ weyl ℤ r r le_rfl ν := by
    intro m
    refine weylRational r r le_rfl ν hν (b m) ?_
    rw [← hspan]
    exact Submodule.subset_span ⟨m, rfl⟩
  choose c hc0 hc using hb
  set Cc : ℤ := ∏ m, c m with hCc
  have hC0 : Cc ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hc0 m
  have hall : ∀ x ∈ dualWeyl ℤ r r ν, Cc • x ∈ weyl ℤ r r le_rfl ν := by
    intro x hx
    rw [← hspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨d, hd⟩ : c m ∣ Cc := Finset.dvd_prod_of_mem c (Finset.mem_univ m)
      rw [hd, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (hc m)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  obtain ⟨D', hD', hnd⟩ := ld_val_split l hl Cc hC0
  refine ⟨padicValInt l Cc, fun μ x hx => ⟨D', hnd, ?_⟩⟩
  have := hall x hx.1
  rwa [hD', mul_comm] at this
end Formalism.CohomologicalDescent.LD
