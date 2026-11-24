-- Prove2me | solution 1 for Formalism.L2.DIV.we_weyl_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:12.331946+00:00
-- url     : https://prove2.me/submissions/b39dd42b-8dad-4cdb-b8dc-1d5f3e14c06e

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LowerTriangularIntegral
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_WeTransposeWordTransposeWord
import Theorems.Thm_Formalism_L2_DIV_we_weyl_le
import Theorems.Thm_Formalism_L2_DIV_we_nabla_fg
import Theorems.Thm_Formalism_L2_DIV_we_span_weyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual


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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.GradedWeylDivisibility
variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
namespace Formalism.L2.DIV
theorem _root_.solution (hν : Antitone ν) :
    Submodule.IsLattice ℚ (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n))) := by
  have himg : (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n))).map
      ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ) = (weyl ℤ r n hn ν).map (intQ r n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, we_weyl_le hn ν hν x hx⟩, hx, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_injective ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
      (dualWeyl ℚ r n ν).injective_subtype ?_
    rw [himg]
    exact (Submodule.FG.of_le (we_nabla_fg r n ν) (weylLeDual ℤ r n hn ν hν)).map _
  · apply Submodule.map_injective_of_injective (f := (dualWeyl ℚ r n ν).subtype) (dualWeyl ℚ r n ν).injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have h2 : ((dualWeyl ℚ r n ν).subtype '' (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n)) : Set (dualWeyl ℚ r n ν))) =
        (((weyl ℤ r n hn ν).map (intQ r n) : Submodule ℤ _) : Set (MvPolynomial (Fin r × Fin n) ℚ)) := by
      conv_rhs => rw [← himg]
      rfl
    rw [h2, we_span_weyl hn ν hν]
end Formalism.L2.DIV
