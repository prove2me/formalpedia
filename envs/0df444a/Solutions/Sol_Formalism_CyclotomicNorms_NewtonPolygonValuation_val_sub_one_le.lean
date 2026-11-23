-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.val_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:23.022955+00:00
-- url     : https://prove2.me/submissions/92cabc9e-5217-4326-b940-b6ef9664315e

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
import Theorems.Thm_Formalism_CyclotomicNorms_NewtonPolygonValuation_val_root_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.NewtonPolygonValuation
variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))
namespace Formalism.CyclotomicNorms.NewtonPolygonValuation
theorem _root_.solution {ζ : L} {N : ℕ} (hN : 0 < N) (hζ : ζ ^ N = 1) (i : ℕ) :
    v (ζ - 1) ≤ v (ζ ^ i - 1) := by
  rw [← geom_sum_mul, AddValuation.map_mul]
  have h0 : (0 : WithTop ℝ) ≤ v (∑ k ∈ range i, ζ ^ k) := by
    apply AddValuation.map_le_sum
    intro k _
    rw [AddValuation.map_pow, val_root_eq_zero v hN hζ, smul_zero]
  calc v (ζ - 1) = 0 + v (ζ - 1) := (zero_add _).symm
    _ ≤ _ := add_le_add h0 le_rfl
end Formalism.CyclotomicNorms.NewtonPolygonValuation
