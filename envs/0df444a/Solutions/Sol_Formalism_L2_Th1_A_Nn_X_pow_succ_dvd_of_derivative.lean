-- Prove2me | solution 1 for Formalism.L2.Th1.A.Nn.X_pow_succ_dvd_of_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:48:39.078523+00:00
-- url     : https://prove2.me/submissions/601cf8f7-508d-4225-a92b-35a4aa998777

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Nn
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.Nn
theorem _root_.solution
    (hR : ∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) {f : R⟦X⟧} {n : ℕ}
    (h0 : constantCoeff f = 0) (h : X ^ n ∣ derivative R f) : X ^ (n + 1) ∣ f := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro m hm
  rcases m with _ | k
  · simpa using h0
  · have hk := h k (by omega)
    rw [PowerSeries.coeff_derivative] at hk
    apply hR (k + 1) _ (Nat.succ_ne_zero k)
    rw [mul_comm]
    exact_mod_cast hk
end Formalism.L2.Th1.A.Nn
