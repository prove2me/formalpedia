-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.vs_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:51.835843+00:00
-- url     : https://prove2.me/submissions/be8202c4-6480-4012-bb36-40c4679da3ba

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_limit_ident
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_limit_ck
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux1_rsmul_cancel__96098f4791bb
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (Mat k r)) :
    IsClosed (Vs E a mm S : Set (Lp k r mm E)) := by
  refine IsSeqClosed.isClosed ?_
  intro xs v hxs hlim
  have hxs' : ∀ n, ∃ F : Mat k r → E, InCC a mm F ∧ (∀ g ∈ GV k r, g ∉ S → F g = 0) ∧
      ⇑(xs n) = Tf a mm F := hxs
  choose Fs hFs using hxs'
  set ε : ℕ → ℝ := fun n => ‖xs n - v‖ with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hlim
  have hε0 : ∀ n, 0 ≤ ε n := fun n => norm_nonneg _
  have hC : ∀ n, CkOn ((mm : ℕ) : ℕ∞) (GV k r) (Fs n) := fun n => (hFs n).1.choose_spec.1
  set K := Kf a (⇑v) with hK
  have hb : ∀ n (u w : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ w, unitLie k r X) →
      u.length + w.length ≤ mm → ∀ g ∈ GV k r, ‖dLR u w (Fs n) g - K u w g‖ ≤ gN g ^ (-a) * ε n := by
    intro n u w hu hw hl g hg
    have h : Vd mm u w g := ⟨hu, hw, hl, hg⟩
    rw [Tf_inv (hFs n).2.2 h, hK, Kf, dif_pos h, ← smul_sub,
      norm_rsmul _ (Real.rpow_nonneg (gN_pos hg).le _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (gN_pos hg).le _)
    have := lp.norm_apply_le_norm (p := ⊤) (by simp) (xs n - v) ⟨((u, w), g), h⟩
    simp only [lp.coeFn_sub, Pi.sub_apply] at this
    exact this
  have hid := limit_ident Fs hC K ε hε hb
  have hck := limit_ck Fs hC K ε hε hε0 hb
  refine ⟨K [] [], ⟨‖v‖, hck, ?_⟩, ?_, ?_⟩
  · intro u w hu hw hl g hg
    have h : Vd mm u w g := ⟨hu, hw, hl, hg⟩
    rw [hid u w hu hw hl g hg, hK, Kf, dif_pos h, norm_rsmul _ (Real.rpow_nonneg (gN_pos hg).le _),
      ← mul_assoc, ← Real.rpow_add (gN_pos hg), add_neg_cancel, Real.rpow_zero, one_mul]
    exact lp.norm_apply_le_norm (by simp) _ _
  · intro g hg hgS
    have h : Vd mm [] [] g := ⟨by simp, by simp, by simp, hg⟩
    have hz : ∀ n, xs n ⟨(([], []), g), h⟩ = 0 := by
      intro n
      rw [(hFs n).2.2]
      show ((gN g ^ a : ℝ) : ℂ) • Fs n g = 0
      rw [(hFs n).2.1 g hg hgS, smul_zero]
    have hv : ‖v ⟨(([], []), g), h⟩‖ ≤ 0 := by
      refine ge_of_tendsto' hε fun n => ?_
      have := lp.norm_apply_le_norm (p := ⊤) (by simp) (xs n - v) ⟨(([], []), g), h⟩
      simp only [lp.coeFn_sub, Pi.sub_apply, hz n, zero_sub, norm_neg] at this
      exact this
    rw [hK, Kf, dif_pos h, norm_le_zero_iff.1 hv, smul_zero]
  · funext i
    obtain ⟨⟨⟨u, w⟩, g⟩, h⟩ := i
    show v ⟨((u, w), g), h⟩ = ((gN g ^ a : ℝ) : ℂ) • dLR u w (K [] []) g
    rw [hid u w h.1 h.2.1 h.2.2.1 g h.2.2.2, hK, Kf, dif_pos h, rsmul_cancel' h.2.2.2]
end Formalism.FourierDecayAlt.P.Ux1
