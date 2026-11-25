-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.stepTwistFromParts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:51:16.865363+00:00
-- url     : https://prove2.me/submissions/a3dcf6d3-8603-4b8a-92d2-23021ccf1f22

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Theorems.Thm_Formalism_FourierDecayAlt_P5_RRw_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P5_commute_io
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_form_mulOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : StepTwistFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hPW hWS hWC hWK w hw l s Wv Wv' hW hW' x y hx hy c _
  refine ⟨hWK w hw l s Wv Wv' hW hW' x hx, fun t _ => ?_⟩
  obtain ⟨hwave, hc1, hc2, hp⟩ := hWS hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    hPW ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hw.1.1
  have hQ : ∀ Y i j, QQi L st l.succ Y i j ∈ Subalgebra.centralizer ℂ {mkP Wv Wv'} := by
    intro Y i j
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (hWC l s Wv Wv' hW hW' Y i j).eq
  have hcomm : io (mkP Wv Wv') * RRi L st l.succ w = RRi L st l.succ w * io (mkP Wv Wv') :=
    (commute_io (RRw_mem _ hQ w)).eq
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) x, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) x,
    ← act_mul (RRi L st l.succ w) (io (mkP Wv Wv')), ← hcomm, act_mul (io (mkP Wv Wv')), form_mulOp μ l s Wv Wv' hW]
  ring
end Formalism.FourierDecayAlt.P5
