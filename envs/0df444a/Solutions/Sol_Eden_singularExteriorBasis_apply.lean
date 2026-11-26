-- Prove2me | solution 1 for Eden.singularExteriorBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:02.752051+00:00
-- url     : https://prove2.me/submissions/d75ff63e-5977-4e27-9ed6-06ebf64f0429

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram

set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : singularExteriorBasis k A s =
      exteriorPower.ιMulti_family ℝ k (singularVectorBasis A) s := by
  change ((singularVectorBasis A).exteriorPower k).toBasis s = _
  rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
  rfl
end Eden
