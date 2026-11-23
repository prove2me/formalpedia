-- Prove2me | solution 1 for Formalism.F.covol_eq_of_linearEquiv_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:51.444434+00:00
-- url     : https://prove2.me/submissions/b29ff17a-5ff0-4db3-8fb0-689b1c350b2a

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Theorems.Thm_Formalism_F_covol_eq_gram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule MeasureTheory
noncomputable section
open Formalism Formalism.F
universe u
namespace Formalism.F
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology M]
    (f : L ≃ₗ[ℤ] M)
    (hf : ∀ x y : L, inner ℝ ((f x : M) : F) ((f y : M) : F) = inner ℝ (x : E) (y : E)) :
    covol M = covol L := by
  classical
  let b := Module.finBasis ℤ L
  rw [covol_eq_gram F M (Fin (Module.finrank ℤ L)) (b.map f), covol_eq_gram E L _ b]
  congr 2
  ext i j
  simp only [Matrix.gram, Matrix.of_apply, Basis.map_apply]
  exact hf (b i) (b j)
end Formalism.F
