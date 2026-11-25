-- Prove2me | solution 1 for CompanionTheory.Bmu.prod_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:18.879062+00:00
-- url     : https://prove2.me/submissions/8f177570-d3c2-4ff1-9126-0db348623c2f

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ProdNormLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CompanionTheory.Bmu
theorem _root_.solution {n : ℕ} (W : List (Mat n)) {a : ℝ} (h : ∀ X ∈ W, ‖X‖ ≤ a) :
    (W.map fun X => ‖X‖).prod ≤ a ^ W.length := by
  induction W with
  | nil => simp
  | cons X W ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    have h0 : 0 ≤ (W.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    exact mul_le_mul (h X List.mem_cons_self) (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY)) h0
      ((norm_nonneg X).trans (h X List.mem_cons_self))
end CompanionTheory.Bmu
