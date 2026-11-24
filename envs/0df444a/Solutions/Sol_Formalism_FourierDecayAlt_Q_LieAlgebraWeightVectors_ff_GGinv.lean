-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ff_GGinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:13.534307+00:00
-- url     : https://prove2.me/submissions/02d81020-cd10-4713-8049-c0001b9b0ead

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_nlev_fix
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_GG_left
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_GG_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_GG_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hGG : ∀ g ∈ D, GGl k r z z' g ≠ 0) {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) :
    (fun x => ((GGl k r z z' x : ℂ))⁻¹ • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  have hcd := ffa_GG_contDiff (k := k) (r := r) z z'
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at hJ ⊢
  obtain ⟨s, l, rr, e⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, o, m, cd, q⟩ := s g₀ hg₀
    have ho : IsOpen {x : Mx k r | (GGl k r z z' x : ℂ) ≠ 0} :=
      isOpen_ne_fun hcd.continuous continuous_const
    refine ⟨U ∩ {x : Mx k r | (GGl k r z z' x : ℂ) ≠ 0}, fun x => ((GGl k r z z' x : ℂ))⁻¹ • F x,
      o.inter ho, ⟨m, Complex.ofReal_ne_zero.mpr (hGG g₀ hg₀.2)⟩, ?_, fun g hg hgl => by rw [q g hg.1 hgl]⟩
    exact ((hcd.contDiffOn.mono Set.inter_subset_left).inv (fun x hx => hx.2)).smul
      (cd.mono Set.inter_subset_left)
  · intro g hg n hn
    have hnz : n *ᵥ z = z := ffa_nlev_fix hn hz
    rw [l g hg n hn, ffa_GG_left hn.1.1 hnz, smul_comm]
  · intro g hg n hn
    have hnz : n *ᵥ z' = z' := ffa_nlev_fix hn hz'
    rw [rr g hg n hn, ffa_GG_right hnz, smul_comm]
  · intro g hg h hh h' hh'
    rw [e g hg h hh h' hh', ffa_GG_right hh'.2.2, ffa_GG_left hh.1 hh.2.2,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
