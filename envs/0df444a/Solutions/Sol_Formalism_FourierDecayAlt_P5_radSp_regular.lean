-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.radSp_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:50:39.753907+00:00
-- url     : https://prove2.me/submissions/377cb89d-844e-4c91-895c-7094177d8d42

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (Φ : RadSp k r z z' π π') (g : Mx k r) (c : Fin r → ℂ) :
    (c ∈ OmX r → DifferentiableAt ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c) ∧
      (c ∉ OmX r → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, -⟩ := hΦm
  refine ⟨fun hc => ?_, fun hc => h0 (c, g) (fun hx => hc (by
    simp only [DomR, Set.mem_setOf_eq] at hx
    exact hx.1))⟩
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g) (by
      simp only [DomR, Set.mem_setOf_eq]
      exact ⟨hc, hg.1, hg.2⟩)
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := by fun_prop
    have hev : ∀ᶠ c' in nhds c, (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = F (c', g) := by
      have hU' : ∀ᶠ c' in nhds c, (c', g) ∈ U := hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
      filter_upwards [hU'] with c' hc'
      exact hΦ (c', g) hc' hg.1
    have hFd : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (c', g)) c := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun c' => F (c', g)) c := hFd.comp c hpair
    exact hcomp.congr_of_eventuallyEq hev
  · have hz : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      refine h0 (c', g) (fun hx => hg ?_)
      simp only [DomR, Set.mem_setOf_eq] at hx
      exact ⟨hx.2.1, hx.2.2⟩
    rw [hz]
    exact differentiableAt_const 0
end Formalism.FourierDecayAlt.P5
