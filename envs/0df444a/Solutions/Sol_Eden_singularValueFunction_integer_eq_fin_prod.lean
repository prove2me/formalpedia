-- Prove2me | solution 1 for Eden.singularValueFunction_integer_eq_fin_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:11.955063+00:00
-- url     : https://prove2.me/submissions/584cc7d0-7211-45a4-b96e-ec977a041f38

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
import Theorems.Thm_Eden_singularValueFunction_integer

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    {k : ℕ} (hk : k ≤ 5) :
    singularValueFunction A k = ∏ i : Fin k, A.singularValues (Fin.castLE hk i) := by
  rw [singularValueFunction_integer A hk, ← Fin.prod_univ_eq_prod_range]
  rfl
end Eden
