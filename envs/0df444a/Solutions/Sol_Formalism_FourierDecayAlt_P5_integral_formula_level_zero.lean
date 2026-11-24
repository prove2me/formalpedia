-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.integral_formula_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:26:06.010497+00:00
-- url     : https://prove2.me/submissions/200a817b-52b7-45da-9878-4ea5938acd7b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_integral_formula_top
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_integral_formula_step

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
theorem _root_.solution (hT : TopIdent (S := S) P z z' π π' μ L st K l0) (hN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hS : SliceIn (S := S) P z z' π π' L st K l0) (hD : StepDens (S := S) P z z' π π' μ L st K l0)
    (hM : TopDensMeas S P z z' π π' μ L st K) : CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 := by
  intro w hw x y hx hy c hc
  have H : ∀ n (i : Fin (P.r + 1)), P.r - i.val = n → LevelIntegralFormula P z z' π π' μ L st K w i := by
    intro n
    induction n with
    | zero =>
      intro i hn
      have hi : i = Fin.last P.r := Fin.ext (by rw [Fin.val_last]; have := i.isLt; omega)
      subst hi
      exact level_integral_formula_top hT w hw
    | succ n ihn =>
      intro i hn
      have hlt : i.val < P.r := by omega
      have hi : i = (⟨i.val, hlt⟩ : Fin P.r).castSucc := Fin.ext rfl
      rw [hi]
      exact level_integral_formula_step hN hS hD hM w hw ⟨i.val, hlt⟩ (ihn _ (by show P.r - (i.val + 1) = n; omega))
  have h0 := H _ 0 rfl x y hx hy c hc
  have hf : levelIntegrand L st w 0 x y c = fun q => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w (act (bTall L w) x) (act (bTall L w) y) (glue 0 c q.1) (Matrix.of q.2) := by
    funext q
    simp only [levelIntegrand, Fin.val_zero, level_product_zero]
  rw [hf] at h0
  exact h0
end Formalism.FourierDecayAlt.P5
