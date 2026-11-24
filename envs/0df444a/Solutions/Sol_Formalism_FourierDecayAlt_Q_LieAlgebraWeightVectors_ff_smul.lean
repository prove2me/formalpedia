-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ff_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:51:49.592266+00:00
-- url     : https://prove2.me/submissions/51b0da51-43c8-4dbb-80e9-e06f02cef5d7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {J : Mx k r → (Wq →L[ℂ] Wp)} (h : J ∈ FFl k r z z' π π' (Fin.last r) D) (c : ℂ) :
    (fun x => c • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at h ⊢
  obtain ⟨s, l, rr, e⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, o, m, cd, q⟩ := s g₀ hg₀
    exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun g hg hgl => by rw [q g hg hgl]⟩
  · intro g hg n hn
    rw [l g hg n hn, smul_comm]
  · intro g hg n hn
    rw [rr g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    rw [e g hg h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
