-- Prove2me | solution 1 for Formalism.L2.DIV.weyl_eq_dual_nabla_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:36.865448+00:00
-- url     : https://prove2.me/submissions/b75b8a8b-a7bb-42e2-9a86-479596463285

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_nabla_eq_dual_weyl_holds
import Theorems.Thm_Formalism_L2_DIV_we_form_symm
import Theorems.Thm_Formalism_L2_DIV_we_form_nondeg
import Theorems.Thm_Formalism_L2_DIV_we_finiteDimensional
import Theorems.Thm_Formalism_L2_DIV_we_cut_inj
import Theorems.Thm_Formalism_L2_DIV_we_cut_bDual
import Theorems.Thm_Formalism_L2_DIV_we_weyl_le
import Theorems.Thm_Formalism_L2_DIV_we_nabla_le
import Theorems.Thm_Formalism_L2_DIV_we_weyl_lattice
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice
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
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.DIV
theorem _root_.solution : WeylEqDualNabla := by
  intro r n hn ν hν
  have hfd := we_finiteDimensional r n ν
  have hdd := (Formalism.HermitianLatticesTheory.dualLattice ℤ ℚ (dualWeyl ℚ r n ν) (weForm hn ν) (we_form_symm hn ν) (we_form_nondeg hn ν)
    (fun z => ⟨z, by simp⟩) _ (we_weyl_lattice hn ν hν)).2.1
  refine we_cut_inj (ν := ν) (we_weyl_le hn ν hν) (fun x hx => hx.1) ?_
  rw [we_cut_bDual hn ν _ (we_nabla_le ν), nabla_eq_dual_weyl_holds r n hn ν hν,
    we_cut_bDual hn ν _ (we_weyl_le hn ν hν), hdd]
end Formalism.L2.DIV
