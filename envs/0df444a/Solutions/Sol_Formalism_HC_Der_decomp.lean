-- Prove2me | solution 1 for Formalism.HC.Der.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:06.901676+00:00
-- url     : https://prove2.me/submissions/bc4fb80d-6ba6-4784-8c8f-6d1525f6f25c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_val_modEq_iff
import Theorems.Thm_Formalism_HC_Der_val_modEq_one_iff
import Theorems.Thm_Formalism_HC_Der_inertia
import Theorems.Thm_Formalism_HC_Der_exists_frob
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_mem_stab_of
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
import Theorems.Thm_Formalism_HC_Der_smul_mem_of_inertia


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), σ ∈ MulAction.stabilizer _ P ↔
      ∃ (u : (ZMod H.condN)ˣ) (k : ℕ), (u : ZMod H.condN).val ≡ l ^ k [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [val_modEq_iff hM] at hw
  constructor
  · intro hσ
    obtain ⟨k, ρ, hρ, rfl⟩ := Decomp.stab_eq_inertia_mul l P F σ hF hσ
    obtain ⟨u, hu, h1⟩ := (inertia H l P ρ).mp hρ
    refine ⟨u * w ^ k, k, ?_, by rw [map_mul, map_mul, map_pow, map_pow, h1, hFw]⟩
    rw [val_modEq_one_iff hM] at hu
    rw [val_modEq_iff hM, map_mul, hu, one_mul, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow]
  · rintro ⟨u, k, hu, h1⟩
    have h2 : ∀ x : 𝓞 H.E, (σ * (F ^ k)⁻¹) • x - x ∈ P := by
      rw [inertia H l P]
      refine ⟨u * (w ^ k)⁻¹, ?_, by rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, h1, hFw]⟩
      rw [val_modEq_iff hM] at hu
      have h3 : ZMod.unitsMap hM u = ZMod.unitsMap hM (w ^ k) :=
        Units.ext (by rw [hu, map_pow, Units.val_pow_eq_pow_val, hw, Nat.cast_pow])
      rw [val_modEq_one_iff hM, map_mul, map_inv, h3, mul_inv_cancel]
    have h4 := Subgroup.mul_mem _ (Decomp.mem_stab_of _ P (smul_mem_of_inertia _ P h2))
      (Subgroup.pow_mem _ hF.mem_stabilizer k)
    rwa [inv_mul_cancel_right] at h4
end Formalism.HC.Der
