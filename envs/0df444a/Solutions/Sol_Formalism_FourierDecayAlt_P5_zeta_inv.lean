-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.zeta_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:35.555659+00:00
-- url     : https://prove2.me/submissions/9e20f5c8-7497-4d0d-ad60-bf13cc436737

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P5_herm_mulVec_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (g : Mx k r) (h h' : Mx k r) (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    zeta k r z z' (h * g * h') = zeta k r z z' g := by
  simp only [UWset, Set.mem_setOf_eq] at hh hh'
  obtain ⟨hU, hb, hz⟩ := hh
  obtain ⟨hU', hb', hz'⟩ := hh'
  simp only [UH, Set.mem_setOf_eq] at hU
  have hf' : h' *ᵥ fvec k r z' (Fin.last r) = fvec k r z' (Fin.last r) := by
    unfold fvec
    rw [dif_neg (by simp)]
    exact hz'
  have hf : h *ᵥ fvec k r z (Fin.last r) = fvec k r z (Fin.last r) := by
    unfold fvec
    rw [dif_neg (by simp)]
    exact hz
  unfold zeta zetaL
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf']
  conv_lhs => rw [← hf]
  exact herm_mulVec_mulVec _ _ hU _ _
end Formalism.FourierDecayAlt.P5
