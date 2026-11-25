-- Prove2me | solution 1 for CompanionTheory.ThKF.E.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:47.748102+00:00
-- url     : https://prove2.me/submissions/f8786694-b687-4a69-bbcf-214a245f707d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
import Theorems.Thm_CompanionTheory_ThKF_E_exists_rho
import Theorems.Thm_CompanionTheory_ThKF_E_toLp_rho
import Theorems.Thm_CompanionTheory_ThKF_E_quad_mem
import Theorems.Thm_GlobalTheory_RealWeil_metaplectic_schwartz_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKF CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKF.E
theorem _root_.solution (hP : GlobalTheory.Published.RealMetaplecticRepresentation) {X : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) : ∃ (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l →L[ℂ] Sch l), Q ∈ weylAlg l ∧
      (∀ f, U 0 f = f) ∧ (∀ s t f, U (s + t) f = U s (U t f)) ∧
      (∀ t, Impl (fun w => NormedSpace.exp (t • X) *ᵥ w) (U t).toLinearMap) ∧
      (∀ f, Continuous fun t => (U t f).toLp 2 volume) ∧
      ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (U t f)) (lam (Q f)) 0 := by
  rcases isEmpty_or_nonempty l with hl | hl
  · refine ⟨fun _ => 1, 0, zero_mem _, fun _ => rfl, fun _ _ _ => rfl, fun t => ⟨fun _ => rfl, fun w f g hg => ?_⟩,
      fun _ => continuous_const, fun f lam => by simpa using hasDerivAt_const _ _⟩
    rw [Subsingleton.elim (NormedSpace.exp (t • X) *ᵥ w) w]
    exact hg
  obtain ⟨G, _, _, _, pr, om, omS, -, h2, h3, h4, h5, h6⟩ := hP l
  obtain ⟨γ, hc, h0, hm, hγ, hd⟩ := h6 X hX
  refine ⟨fun t => omS (γ t), quad X, quad_mem X, fun f => by simp [h0], fun s t f => by simp [hm], fun t => ⟨fun f => ?_,
    fun w f g hg => ?_⟩, fun f => ?_, fun f lam => (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hγ hd f⟩
  · show ‖(omS (γ t) f).toLp 2 volume‖ = _
    rw [← h4, LinearIsometryEquiv.norm_map]
  · obtain ⟨g', hg'⟩ := exists_rho (NormedSpace.exp (t • X) *ᵥ w) (omS (γ t) f)
    have : omS (γ t) g = g' := by
      apply injective_toLp 2 volume
      show (omS (γ t) g).toLp 2 volume = g'.toLp 2 volume
      rw [← h4, toLp_rho hg, toLp_rho hg', h3, hγ, h4]
    exact this ▸ hg'
  · simp only [← h4]
    exact (h2 _).comp hc
end CompanionTheory.ThKF.E
