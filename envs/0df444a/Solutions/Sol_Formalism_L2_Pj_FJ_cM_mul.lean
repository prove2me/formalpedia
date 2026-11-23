-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.cM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:36.246896+00:00
-- url     : https://prove2.me/submissions/b6235f8a-17b5-4b03-96db-7f12a55b88e4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution {m n o : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    cM (A * B) = cM A * cM B := by
  simp only [cM]
  exact Matrix.map_mul
end Formalism.L2.Pj.FJ
