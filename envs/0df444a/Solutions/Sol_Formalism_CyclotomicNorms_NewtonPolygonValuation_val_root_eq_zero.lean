-- Prove2me | solution 1 for Formalism.CyclotomicNorms.NewtonPolygonValuation.val_root_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:38.403525+00:00
-- url     : https://prove2.me/submissions/c1747161-515c-4ae8-8643-5709dbd3f8b9

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton

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
theorem _root_.solution {z : L} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : v z = 0 := by
  have h := congrArg v hz
  rw [AddValuation.map_pow, AddValuation.map_one] at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact zero_ne_one hz
  have hne : v z ≠ ⊤ := (AddValuation.ne_top_iff v).2 hz0
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hr] at h ⊢
  rw [← WithTop.coe_nsmul] at h
  have h1 : N • r = 0 := by exact_mod_cast h
  rw [nsmul_eq_mul] at h1
  have hr0 : r = 0 := by
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hN.ne')
    · exact h2
  rw [hr0]
  rfl
end Formalism.CyclotomicNorms.NewtonPolygonValuation
