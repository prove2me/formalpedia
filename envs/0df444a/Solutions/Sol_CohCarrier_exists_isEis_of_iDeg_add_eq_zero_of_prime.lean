-- Prove2me | solution 1 for CohCarrier.exists_isEis_of_iDeg_add_eq_zero_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e858f914-93dc-54e6-bc5e-f8abd58dc473

import Mathlib
import Definitions.Def_CohCarrier_Tower

import Theorems.Thm_CohCarrier_isEis_kernel_pair_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero_of_prime
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply"

set_option autoImplicit false

namespace CohCarrier
p2m_export "CohCarrier" "IsEis H1 heckeT LevelLE iDeg' isEis_kernel_pair_of_prime"
namespace ExistsIsEisOfPrimeBridge
p2m_open "CohCarrier"

theorem isEis_iff_nsmul (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A) :
    IsEis R A M H ℓ₀ F ↔ heckeT M H ℓ₀ A F = ℓ₀ • F + F := by
  unfold IsEis
  rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]

theorem isEis_of_isEis (R : Type*) [CommRing R] (S : Type*) [CommRing S]
    (A : Type) [AddCommGroup A] [Module R A] [Module S A]
    (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ₀ : ℕ) [NeZero ℓ₀] (F : H1 M H A)
    (hF : IsEis S A M H ℓ₀ F) : IsEis R A M H ℓ₀ F :=
  (isEis_iff_nsmul R A M H ℓ₀ F).2 ((isEis_iff_nsmul S A M H ℓ₀ F).1 hF)

end CohCarrier.ExistsIsEisOfPrimeBridge

set_option linter.unusedVariables false in
open _root_.CohCarrier _root_.P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero_of_prime.CohCarrier in
theorem solution
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (hqp : q.Prime) (hqN : ¬ q ∣ N) (hA : ∀ a : A, q • a = 0 → a = 0)
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q) (x z' : H1 (N * q) ⊤ A)
    (hxz : iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0) :
    ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
      IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w) := by
  obtain ⟨w, hz, hx⟩ :=
    (CohCarrier.isEis_kernel_pair_of_prime ℤ A ℓ₀ N q h₁ hq h₁' hq' hqp hqN hℓ hℓNq).2 x z' hxz
  exact ⟨w, ExistsIsEisOfPrimeBridge.isEis_of_isEis R ℤ A (N * q) ⊤ ℓ₀ _ hz,
    ExistsIsEisOfPrimeBridge.isEis_of_isEis R ℤ A (N * q) ⊤ ℓ₀ _ hx⟩

end S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero_of_prime
end P2MW
export P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero_of_prime (solution)
