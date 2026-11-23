-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.divisor_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:45.804925+00:00
-- url     : https://prove2.me/submissions/d56314c0-4dc7-432c-b678-6f2c6e9a0536

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
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : DivisorCount := by
  intro K _ _ I
  refine UniqueFactorizationMonoid.induction_on_prime (P := fun I : Ideal (NumberField.RingOfIntegers K) =>
    I ≠ ⊥ → {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.Finite ∧
    {J : Ideal (NumberField.RingOfIntegers K) | J ∣ I}.ncard ≤ Ideal.absNorm I) I ?_ ?_ ?_
  · intro h; exact absurd Ideal.zero_eq_bot h
  · intro x hx _
    have hx' : x = ⊤ := Ideal.isUnit_iff.1 hx
    have : {J : Ideal (NumberField.RingOfIntegers K) | J ∣ x} = {⊤} := by
      ext J
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h; exact Ideal.isUnit_iff.1 (isUnit_of_dvd_unit h hx)
      · rintro rfl; rw [hx']
    rw [this, hx']
    simp
  · intro a p ha hp ih _
    obtain ⟨hfin, hle⟩ := ih (by rwa [← Ideal.zero_eq_bot])
    have hsub : {J : Ideal (NumberField.RingOfIntegers K) | J ∣ p * a}
        ⊆ {J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a} := by
      intro J hJ
      by_cases hpJ : p ∣ J
      · obtain ⟨J', rfl⟩ := hpJ
        exact Or.inr ⟨J', (mul_dvd_mul_iff_left hp.ne_zero).1 hJ, rfl⟩
      · left
        obtain ⟨c, hc⟩ := hJ
        have : p ∣ J * c := ⟨a, hc.symm⟩
        rcases hp.dvd_or_dvd this with h | ⟨c', rfl⟩
        · exact absurd h hpJ
        · refine ⟨c', ?_⟩
          apply mul_left_cancel₀ hp.ne_zero
          rw [hc]; ring
    have hfin2 : ({J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a}).Finite := hfin.union (hfin.image _)
    refine ⟨hfin2.subset hsub, ?_⟩
    have hp2 : 2 ≤ Ideal.absNorm p := by
      have h0 : Ideal.absNorm p ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]; exact hp.ne_zero
      have h1 : Ideal.absNorm p ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff, ← Ideal.isUnit_iff]; exact hp.not_isUnit
      omega
    calc _ ≤ ({J | J ∣ a} ∪ (fun J => p * J) '' {J | J ∣ a}).ncard := Set.ncard_le_ncard hsub hfin2
      _ ≤ {J | J ∣ a}.ncard + ((fun J => p * J) '' {J | J ∣ a}).ncard := Set.ncard_union_le _ _
      _ ≤ {J | J ∣ a}.ncard + {J | J ∣ a}.ncard := by
          exact Nat.add_le_add_left (Set.ncard_image_le hfin) _
      _ = 2 * {J | J ∣ a}.ncard := by ring
      _ ≤ Ideal.absNorm p * Ideal.absNorm a := Nat.mul_le_mul hp2 hle
      _ = _ := (map_mul _ _ _).symm
end Formalism.HermitianLatticeCounting.P.S4aux
