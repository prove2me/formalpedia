-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_positive_semidefinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:05:13.689201+00:00
-- url     : https://prove2.me/submissions/c2fce837-eaaf-4741-81fd-2e1b625d2af7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTop
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopPSD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt NumberField MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Top.TopPSDT := by
  intro Wp Wq _ _ _ _ _ P l0 T ν' m₀ Θ TP f χ admitted ε hε w hw hne Y
  unfold TB.PSDOn
  set F := D.cutF T.base χ f ε
  set dd := Top.dH P l0 (Formalism.QuantumDeterminants.Tz P.k P.r T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r T.base.z') w

  let X : Wd.Ix (Fin w.length) → M.Ty P → C.LPt → (Wq →L[ℂ] Wp) :=
    fun e ρ p => (TP.E ρ).comp (D.vecV T.base ν' m₀ (Θ.Θ w e F) p)
  let g : Wd.Ix (Fin w.length) → M.Ty P → Matrix Y Y ℂ := fun e ρ =>
    Matrix.of fun x y => ((dd (x : C.LPt) e ρ * dd (y : C.LPt) e ρ : ℝ) : ℂ) * B.hsInner (X e ρ x) (X e ρ y)
  have hterm : ∀ e ρ, (g e ρ).PosSemidef := by
    intro e ρ
    let v : Y → _ := fun x => ((dd (x : C.LPt) e ρ : ℝ) : ℂ) • B.hsVec (X e ρ x)
    have h := (Matrix.posSemidef_gram ℂ v).transpose
    have heq : g e ρ = (Matrix.gram ℂ v).transpose := by
      ext x y
      simp only [g, v, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply, inner_smul_left,
        inner_smul_right, B.hsInner, Complex.conj_ofReal]
      push_cast
      ring
    rw [heq]
    exact h
  have hsum : (Matrix.of fun x y : Y => Top.topOf P l0 T ν' m₀ Θ TP F w x y) = ∑ e, ∑ ρ, g e ρ := by
    ext x y
    simp [g, X, dd, Top.topOf, Matrix.sum_apply]
  rw [hsum]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun e _ => ?_)
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun ρ _ => hterm e ρ)
end Formalism.FourierDecayAlt.P
