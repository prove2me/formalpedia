-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_integral_formula_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:34.853849+00:00
-- url     : https://prove2.me/submissions/0b0a5f09-d346-48b7-9cf0-72db922badae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_of_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_one_hermitian_curvature
import Theorems.Thm_Formalism_FourierDecayAlt_P5_glue_last_level
import Theorems.Thm_Formalism_FourierDecayAlt_P5_integral_top_level_point


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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (hT : TopIdent (S := S) P z z' π π' μ L st K l0) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) : LevelIntegralFormula P z z' π π' μ L st K w (Fin.last P.r) := by
  intro x y hx hy c hc
  obtain ⟨hI, hE⟩ := hT w hw x y hx hy c hc
  have hf : levelIntegrand L st w (Fin.last P.r) x y c = fun q => topDens L st w x y c (Matrix.of q.2) := by
    funext q
    simp only [levelIntegrand, Fin.val_last, level_product_of_ge L w P.r le_rfl, act_one_hermitian_curvature, glue_last_level]
    haveI : IsEmpty {l : Fin P.r // P.r ≤ l.val} := ⟨fun l => by have := l.1.isLt; have := l.2; omega⟩
    rw [Fintype.prod_empty]
    simp
  have hT' := integral_top_level_point μ (fun q : Cf P.r (Fin.last P.r) × Mt P.k P.r => topDens L st w x y c (Matrix.of q.2))
  rw [hf]
  exact ⟨hT'.1.2 hI, hE.trans hT'.2.symm⟩
end Formalism.FourierDecayAlt.P5
