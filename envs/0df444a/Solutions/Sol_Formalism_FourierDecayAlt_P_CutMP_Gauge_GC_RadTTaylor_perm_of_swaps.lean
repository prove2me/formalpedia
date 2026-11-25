-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.perm_of_swaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:16:28.87712+00:00
-- url     : https://prove2.me/submissions/c30a6544-d983-4c96-a65b-9f72ef06ae11

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W)
    (h : ∀ (a b : Fin n), a ≠ b → ∀ v : Fin n → E, T (v ∘ Equiv.swap a b) = T v) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), T (v ∘ σ) = T v := by
  classical
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro v; rfl
  | swap_mul f x y hxy ih =>
    intro v
    rw [Equiv.Perm.coe_mul]
    calc T (v ∘ (⇑(Equiv.swap x y) ∘ ⇑f)) = T ((v ∘ Equiv.swap x y) ∘ f) := rfl
      _ = T (v ∘ Equiv.swap x y) := ih _
      _ = T v := h x y hxy v
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
