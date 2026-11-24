-- Prove2me | solution 1 for Formalism.HN.gramBlock_gram_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:25.474412+00:00
-- url     : https://prove2.me/submissions/c4a34602-0798-4cd6-b006-58c595f0d47b

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : E →ₗ[ℝ] F) (f : ι → E) (M : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => g (∑ i, M i j • f i)) = M.transpose * Matrix.gram ℝ (fun i => g (f i)) * M := by
  ext j l
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end Formalism.HN
