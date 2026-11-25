-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:53:03.275307+00:00
-- url     : https://prove2.me/submissions/c1c7ddaa-b627-48e2-ba18-3c90b98a0484

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {R : Type} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution {σ τ : Type} {w : τ → ℕ} (f : σ → τ) {p : MvPolynomial σ R} {D : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) p D) : IsWeightedHomogeneous w (rename f p) D := by
  intro dd hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero f p dd hd
  rw [← h hu, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rfl
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
