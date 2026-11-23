-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.prod_mul_list
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:10.415467+00:00
-- url     : https://prove2.me/submissions/5e01c571-b97c-4682-a057-d2c54c74a3eb

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {R ι : Type} [Monoid R]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (x y : ι → R) (L : List ι)
    (h2 : L.Pairwise fun σ τ => Commute (y σ) (x τ)) :
    (L.map fun σ => x σ * y σ).prod = (L.map x).prod * (L.map y).prod := by
  induction L with
  | nil => simp
  | cons σ L ih =>
    have hp := List.pairwise_cons.mp h2
    have hC : Commute (y σ) (L.map x).prod :=
      Commute.list_prod_right _ _ (by
        intro t ht
        obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp ht
        exact hp.1 τ hτ)
    have key : x σ * y σ * ((L.map x).prod * (L.map y).prod)
        = x σ * (L.map x).prod * (y σ * (L.map y).prod) := by
      calc x σ * y σ * ((L.map x).prod * (L.map y).prod)
          = x σ * (y σ * (L.map x).prod) * (L.map y).prod := by simp only [mul_assoc]
        _ = x σ * ((L.map x).prod * y σ) * (L.map y).prod := by rw [hC.eq]
        _ = x σ * (L.map x).prod * (y σ * (L.map y).prod) := by simp only [mul_assoc]
    simpa only [List.map_cons, List.prod_cons, ih hp.2, mul_assoc] using key
end Formalism.FourierDecayAlt.P.Wd8
