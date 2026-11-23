-- Prove2me | solution 1 for Formalism.CyclotomicNorms.low_coeff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:53.421791+00:00
-- url     : https://prove2.me/submissions/3dee3397-399d-4a50-9bf1-7ab006d917d1

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_LowDegreePowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.CyclotomicNorms
namespace Formalism.CyclotomicNorms
theorem _root_.solution {O : Type*} [CommRing O] (a : O) (M : ℕ) (f : PowerSeries O)
    (hf : f ∈ Ideal.span {PowerSeries.C a, (PowerSeries.X : PowerSeries O) ^ (M + 1)})
    (k : ℕ) (hk : k ≤ M) : a ∣ coeff k f := by
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hf
  rw [map_add, mul_comm u, coeff_C_mul, mul_comm v, coeff_X_pow_mul', if_neg (by omega), add_zero]
  exact dvd_mul_right a _
end Formalism.CyclotomicNorms
