-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.bridge_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:29:32.572922+00:00
-- url     : https://prove2.me/submissions/89834ca9-9fe1-401e-897a-1feb8dca4425

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_bridge_fold
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g)
    {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (qminor Λ p q u) f g = qminorOp Op p q u f g := by
  intro g hg
  simp only [qminor, ev, Formalism.QuantumDeterminants.qminorOp, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hb := bridge_fold Eop hC hL hA hS hΛ Op hLop hT
    (List.ofFn fun j => (u - ((j : ℕ) : ℂ), p (σ j), q j)) f (by simpa using hf) g hg
  simp only [List.map_ofFn, Function.comp_def, ev] at hb
  simp [hb, Int.cast_smul_eq_zsmul]
end Formalism.FourierDecayAlt.P.JFxE
