-- Prove2me | solution 1 for Formalism.HC.Der.frob_any
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:07.769295+00:00
-- url     : https://prove2.me/submissions/72110d62-0d0e-4b9f-9f88-6ab8ab4eef5f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_val_modEq_iff
import Theorems.Thm_Formalism_HC_Der_val_modEq_one_iff
import Theorems.Thm_Formalism_HC_Der_inertia
import Theorems.Thm_Formalism_HC_Der_frob_of_modEq
import Theorems.Thm_Formalism_HC_Der_exists_frob
import Theorems.Thm_Formalism_HC_Der_frob_iff_inertia


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
    (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔
      ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal σ = H.art u := by
  intro l _ P _ _ σ
  refine ⟨fun hσ => ?_, fun ⟨u, h1, h2⟩ => frob_of_modEq H l P σ u h1 h2⟩
  obtain ⟨F, w, hF, hw, hFw⟩ := exists_frob H l P
  have hM := Nat.ordCompl_dvd H.condN l
  rw [frob_iff_inertia P F σ hF, inertia H l P, map_mul, map_inv, hFw] at hσ
  obtain ⟨u, hu, h1⟩ := hσ
  refine ⟨u * w, ?_, by rw [map_mul, ← h1, inv_mul_cancel_right]⟩
  rw [val_modEq_one_iff hM] at hu
  rw [val_modEq_iff hM] at hw ⊢
  rw [map_mul, hu, one_mul, hw]
end Formalism.HC.Der
