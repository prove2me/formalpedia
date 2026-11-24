-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.discr_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:14.303126+00:00
-- url     : https://prove2.me/submissions/ccee154f-b2f3-4437-bbe5-807f3c4798ea

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_finrank_two
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_absNorm_different
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_totallyReal_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    discr ℚ⟮z + z⁻¹⟯ = 2 ^ (2 ^ e * (e + 1) - 1) := by
  have hK := IsCyclotomicExtension.Rat.discr_prime_pow 2 (e + 2) K
  have hexp : 2 ^ (e + 2 - 1) * ((2 - 1) * (e + 2) - 1) = 2 ^ (e + 1) * (e + 1) := by
    rw [show e + 2 - 1 = e + 1 by omega, show (2 - 1) * (e + 2) - 1 = e + 1 by omega]
  have hKabs : (discr K).natAbs = 2 ^ (2 ^ (e + 1) * (e + 1)) := by
    rw [hK, hexp]
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hF := NumberField.absNorm_differentIdeal ℚ⟮z + z⁻¹⟯ (𝓞 ℚ⟮z + z⁻¹⟯)
  have hKd := NumberField.absNorm_differentIdeal K (𝓞 K)
  have htower := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K)
  have hn : Module.finrank (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 ℚ⟮z + z⁻¹⟯) ℚ⟮z + z⁻¹⟯ (𝓞 K) K).symm.trans (finrank_two hz)
  have hmap : Ideal.absNorm (Ideal.map (algebraMap (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K))
      (differentIdeal ℤ (𝓞 ℚ⟮z + z⁻¹⟯))) = (discr ℚ⟮z + z⁻¹⟯).natAbs ^ 2 := by
    rw [← Ideal.absNorm_relNorm (𝓞 ℚ⟮z + z⁻¹⟯) (𝓞 K), Ideal.relNorm_algebraMap, hn, map_pow, hF]
  have heq : (discr K).natAbs = 4 * (discr ℚ⟮z + z⁻¹⟯).natAbs ^ 2 := by
    rw [← hKd, htower, map_mul, absNorm_different hz, hmap]
  have hN : 1 ≤ 2 ^ e * (e + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h4 : 4 * (discr ℚ⟮z + z⁻¹⟯).natAbs ^ 2 = 4 * (2 ^ (2 ^ e * (e + 1) - 1)) ^ 2 := by
    rw [← heq, hKabs, ← pow_mul, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    have hx : 2 ^ (e + 1) * (e + 1) = 2 * (2 ^ e * (e + 1)) := by ring
    rw [hx]
    generalize 2 ^ e * (e + 1) = N at hN ⊢
    omega
  have hd : (discr ℚ⟮z + z⁻¹⟯).natAbs = 2 ^ (2 ^ e * (e + 1) - 1) :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
      (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h4)
  have htr := totallyReal_F hz
  have hsign := NumberField.sign_discr ℚ⟮z + z⁻¹⟯
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, Int.sign_eq_one_iff_pos] at hsign
  rw [← Int.natAbs_of_nonneg hsign.le, hd]
  push_cast
  rfl
end Formalism.FrobeniusOrbits.Discr
