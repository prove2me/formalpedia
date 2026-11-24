-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_product_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:24:55.055114+00:00
-- url     : https://prove2.me/submissions/5cb6831b-7e55-4842-9c4d-e5f62ae2a704

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_eq_list_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) :
    levelProduct L w 0 = bTall L w := by
  have hfr : (List.finRange r).map Fin.val = List.range r := by
    first
    | exact List.map_val_finRange r
    | exact List.map_coe_finRange r
    | exact List.map_coe_finRange
    | simp
  rw [level_product_eq_list_prod L w r 0 (Nat.sub_zero r) (Nat.zero_le r), bTall, ← List.range_eq_range',
    ← hfr, List.map_reverse, List.map_map, List.map_reverse]
  congr 2
  apply List.map_congr_left
  intro j _
  simp [j.isLt]
end Formalism.FourierDecayAlt.P5
