-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.norm_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:37.743352+00:00
-- url     : https://prove2.me/submissions/5d429069-6316-4b59-a484-64fa9eed5bf9

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank K L = 2) (a : L) (ha0 : a ≠ 0)
    (ha : a ^ Fintype.card K = a) : ∃ lam : L, lam ^ (Fintype.card K + 1) = a := by
  classical
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = Units.mk0 a ha0 :=
    Submonoid.mem_powers_iff _ _ |>.1 (mem_powers_iff_mem_zpowers.2 (hg _))
  have hord : orderOf g = (Fintype.card K + 1) * (Fintype.card K - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
      card_L h2]
    obtain ⟨c, hc⟩ : ∃ c, Fintype.card K = c + 1 := ⟨Fintype.card K - 1, by omega⟩
    rw [hc]
    simp only [Nat.add_sub_cancel]
    have : (c + 1) ^ 2 = (c + 1 + 1) * c + 1 := by ring
    omega
  have h1 : (Units.mk0 a ha0) ^ (Fintype.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have : a ^ (Fintype.card K - 1) * a = 1 * a := by
      rw [← pow_succ, one_mul]
      have : Fintype.card K - 1 + 1 = Fintype.card K := by omega
      rw [this, ha]
    exact mul_right_cancel₀ ha0 this
  rw [← hk, ← pow_mul] at h1
  have h3 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h3
  have h4 : (Fintype.card K + 1) ∣ k := Nat.dvd_of_mul_dvd_mul_right (by omega) h3
  obtain ⟨k', rfl⟩ := h4
  refine ⟨((g ^ k' : Lˣ) : L), ?_⟩
  have := congrArg Units.val hk
  rw [Units.val_mk0] at this
  rw [← this, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
end Formalism.HermitianLatticeCounting.P.S4aux
