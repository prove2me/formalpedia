-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.tval_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:32.652324+00:00
-- url     : https://prove2.me/submissions/8637ed32-d059-45f3-925f-44e16c722aea

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
theorem _root_.solution {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hF : CkOn ⊤ (U ∩ GV k r) F) {x : Bool × Mat k r} (hx : inLie k r x.2)
    (t : Tm k r) (hws : ∀ i, ∀ y ∈ t.ws i, inLie k r y.2) {g : Mat k r} (hgU : g ∈ U) (hg : g ∈ GV k r) :
    HasDerivAt (fun s : ℝ => tval Ψ F t (crv x g s)) (((tnext x t).map fun t' => tval Ψ F t' g).sum) 0 := by
  have hg' : g ∈ U ∩ GV k r := ⟨hgU, hg⟩
  have hF1 : ∀ n : ℕ∞, CkOn n (U ∩ GV k r) F := fun n => CkOn_mono le_top hF
  have hA : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ t.j Ψ (F (crv x g s)))
      (fderiv ℝ (iteratedFDeriv ℝ t.j Ψ) (F g) (Dx x F g)) 0 := by
    have h1 := CkOn_diff hx (hF1 1) hg' hg
    have hlt : ((t.j : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _)
    have h2 : HasFDerivAt (iteratedFDeriv ℝ t.j Ψ) (fderiv ℝ (iteratedFDeriv ℝ t.j Ψ) (F g))
        (F (crv x g 0)) := by
      rw [crv_zero]
      exact ((hΨ.differentiable_iteratedFDeriv hlt) (F g)).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hv : ∀ i, HasDerivAt (fun s : ℝ => Dw (t.ws i) F (crv x g s)) (Dw (x :: t.ws i) F g) 0 := by
    intro i
    exact CkOn_diff hx (CkOn_Dw (hws i) (hF1 _)) hg' hg
  have hD := (hA.hasFDerivAt).continuousMultilinearMap_apply (fun i => (hv i).hasFDerivAt)
  refine hD.hasDerivAt.congr_deriv ?_
  simp only [crv_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul, ContinuousMultilinearMap.apply_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [tnext, List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1
  funext l
  by_cases h : l = i
  · subst h
    simp
  · simp [Function.update_apply, h]
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
