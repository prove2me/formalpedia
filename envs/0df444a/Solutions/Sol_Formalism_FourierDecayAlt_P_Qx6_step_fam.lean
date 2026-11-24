-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.step_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:27.441228+00:00
-- url     : https://prove2.me/submissions/f39beaa2-9679-4618-b6ff-e96baeda4082

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_open_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_open_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_open_Dcell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Dcell_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_dom_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_dom_Dcell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_update_mem_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_ev_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_fam_Res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_RS_stepOp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hCS : ChainStep) (hR : ResMem) (hFO : FamOps) (hTP : TPreservesFF) (hLL : TLinLoc) (hW : WeylLevelElementFacts)
    (hz : inWb k r z) (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsDom k r z z' 0 D) (l : Fin r) (Y : ℂ)
    (a b : Fin 2) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamFF k r z z' π π' l.castSucc (Dcell D l.castSucc) Φ)
    (hI : Ind l.val Φ) {c₀ : Fin r → ℂ} (hc₀ : c₀ ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r l.succ)
    (hgD : g ∈ Dcell D l.succ c₀) :
    stepOp z z' l Y a b (Res k r l Φ) c₀ g = Res k r l (QL k r z z' l.castSucc Y a b Φ) c₀ g := by
  set D' := Dcell D l.castSucc c₀ with hD'
  have hdom' : IsDom k r z z' l.castSucc D' := dom_Dcell hR hz hz' hD _ c₀ hc₀
  set S : Set (Fin r → ℂ) := {c | c ∈ OmX r ∧ ∀ a : Fin r, a.val < l.val → c a = c₀ a} with hSdef
  have hS : SData z z' l.succ (Dcell D l.succ) (stepD l (fun _ => D')) S := by
    refine ⟨open_Dcell hD.1 _, open_step l (open_const hdom'.1), dom_Dcell hR hz hz' hD _,
      fun c hc => dom_step hR hz hz' l hdom' (hc l), fun c hc => hc.1, ?_⟩
    intro c hc
    rw [Dcell_succ]
    show {g | w1 k r l (c l) * g ∈ Dcell D l.castSucc c} = {g | w1 k r l (c l) * g ∈ D'}
    rw [hD', Dcell_congr D (i := l.castSucc) (c := c) (c' := c₀) (fun a ha => hc.2 a ha)]
  have hSl : ∀ c ∈ S, ∀ᶠ s in 𝓝 (c l), Function.update c l s ∈ S := by
    intro c hc
    filter_upwards [ev_ne hc.1 l] with s hs
    refine ⟨update_mem_Om hc.1 l hs, fun a ha => ?_⟩
    have hne : a ≠ l := fun e => by rw [e] at ha; exact lt_irrefl _ ha
    rw [Function.update_of_ne hne]
    exact hc.2 a ha
  have hJ₀ := hΦ.2 c₀ hc₀
  have hrel : RS z z' π π' l.succ (Dcell D l.succ) (stepD l (fun _ => D')) S (Res k r l Φ) (res1 k r l (Φ c₀)) := by
    refine ⟨?_, (hR Wp Wq k r z z' π π' l D' hz hz' hdom' (Φ c₀) hJ₀).2, ?_⟩
    · rw [Dcell_succ]
      exact fam_Res hW hR hz hz' l (dom_Dcell hR hz hz' hD _) hΦ
    · intro c hc x _ _
      show _ • Φ c _ = _ • Φ c₀ _
      rw [hI c hc.1 c₀ hc₀ hc.2]
  have h1 := (RS_stepOp hFO hTP hLL hz hz' l hS hSl Y a b _ _ hrel).2.2 c₀ ⟨hc₀, fun _ _ => rfl⟩ g hg hgD
  rw [h1]
  have hgD' : w1 k r l (c₀ l) * g ∈ D' := by
    rw [Dcell_succ] at hgD
    exact hgD
  exact (hCS Wp Wq k r z z' π π' l D' Y a b hz hz' hdom' (Φ c₀) hJ₀ c₀ hc₀ g hg hgD').symm
end Formalism.FourierDecayAlt.P.Qx6
