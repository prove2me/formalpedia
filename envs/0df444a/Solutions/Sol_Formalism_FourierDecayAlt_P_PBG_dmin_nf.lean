-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.dmin_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:05:20.473919+00:00
-- url     : https://prove2.me/submissions/807b396b-d0d1-43fc-898f-7acd3c2dc293

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_det_upper_minor_eq_minor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (x₁ : Q.Mx k r) (i0 s : ℕ) (hh : Matrix (Fin i0) (Fin i0) ℂ) (τ : ℂ)
    (hj : i0 + s ≤ r)
    (hnf : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 + s →
      xi0 x₁ a p = if p.val < i0 + s then C3.Zb i0 s hh τ a.val p.val else 0)
    (n : ℕ) (hn : n ≤ i0 + s) :
    Dmin k r z z' x₁ ⟨n, by omega⟩ = C3.Dlead i0 s hh τ n := by
  rw [← det_upper_minor_eq_minor z z' x₁ n (by omega)]
  unfold C3.Dlead
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [hnf _ _ (by simp; omega), if_pos (by simp [C3.xR, eI]; omega)]
  simp [C3.xR, eI]
end Formalism.FourierDecayAlt.P.PBG
