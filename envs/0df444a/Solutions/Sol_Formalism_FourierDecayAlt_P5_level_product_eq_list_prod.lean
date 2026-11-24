-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_product_eq_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:57:49.540809+00:00
-- url     : https://prove2.me/submissions/00119486-2200-470b-90ba-d3026c99a91a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_of_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_of_ge

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
theorem _root_.solution (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (n : ℕ) :
    ∀ i, r - i = n → i ≤ r →
    levelProduct L w i = ((List.range' i n).reverse.map fun j => if h : j < r then bTl L ⟨j, h⟩ w else 1).prod := by
  induction n with
  | zero =>
    intro i hn hi
    rw [level_product_of_ge L w i (by omega)]
    simp
  | succ n ihn =>
    intro i hn hi
    have hlt : i < r := by omega
    rw [level_product_of_lt L w i hlt, ihn (i + 1) (by omega) (by omega), List.range'_succ, List.reverse_cons,
      List.map_append, List.prod_append]
    simp [hlt]
end Formalism.FourierDecayAlt.P5
