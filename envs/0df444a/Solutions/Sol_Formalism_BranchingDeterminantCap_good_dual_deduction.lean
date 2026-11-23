-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.good_dual_deduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:33.719852+00:00
-- url     : https://prove2.me/submissions/fb51c6e1-6629-4f80-90eb-c997ffebdced

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
import Theorems.Thm_Formalism_BranchingDeterminantCap_GoodDualLattice_dual_exists
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open GoodDualLattice
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : GoodDualDed := by
  intro K V _ _ _ _ _ _ _ _ h hnd e he hsa A hfg hsp
  have hee : ∀ x, e (e x) = e x := fun x => LinearMap.congr_fun he x
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_map, Formalism.HermitianLatticesTheory.dualBasic_mem_dual,
    Submodule.restrictScalars_mem, LinearMap.mem_range, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨hx, x0, rfl⟩
    exact dual_exists h hnd e hee hsa A hfg hsp (e x0) (hee x0)
      (fun y hy hye => hx y ⟨hy, y, hye⟩)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, z, rfl⟩
    rintro y ⟨hyA, w, rfl⟩
    rw [← hsa, hee]
    exact hz _ hyA
end Formalism.BranchingDeterminantCap
