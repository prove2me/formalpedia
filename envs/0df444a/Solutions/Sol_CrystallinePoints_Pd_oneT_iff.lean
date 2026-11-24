-- Prove2me | solution 1 for CrystallinePoints.Pd.oneT_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:28.71118+00:00
-- url     : https://prove2.me/submissions/20d18abb-6064-4d48-87da-e479099ab3c1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoincareDeRhamDuality_DeRhamPerfectPairing_ResSurjD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct
open CrystallinePoints CrystallinePoints.Pd
namespace CrystallinePoints.Pd
theorem _root_.solution {R : Type} [CommRing R] (m : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (y : M) : (1 : R ⧸ m) ⊗ₜ[R] y = 0 ↔ y ∈ m • (⊤ : Submodule R M) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul M m).map_eq_zero_iff, ← Submodule.Quotient.mk_eq_zero]
  have : TensorProduct.quotTensorEquivQuotSMul M m ((1 : R ⧸ m) ⊗ₜ[R] y) = Submodule.Quotient.mk y := by
    have := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) m 1 y
    rwa [map_one, one_smul] at this
  rw [this]
end CrystallinePoints.Pd
