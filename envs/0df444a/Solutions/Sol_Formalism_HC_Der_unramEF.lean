-- Prove2me | solution 1 for Formalism.HC.Der.unramEF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:09.670237+00:00
-- url     : https://prove2.me/submissions/4e4b1747-c1e6-41d5-8c0c-351fb28111b9

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_exists_prime_liesOver
import Theorems.Thm_Formalism_HC_Der_cc_ne_one
import Theorems.Thm_Formalism_HC_Der_inertia_d
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sqrt_fixed
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_D7_inertia_d
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → P ≠ ⊥ → ¬ ∀ x : 𝓞 H.E, H.conj • x - x ∈ P := by
  intro P hP hP0 h
  obtain ⟨p, hp, hpl⟩ := exists_prime_liesOver P hP0
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : H.gal H.conj = φ.cc := MulEquiv.apply_symm_apply _ _
  have hcs : H.conj H.sqd = -H.sqd := by
    rw [H.gal_sqd H.conj, h2]
    simp [Frame.cc, c0]
  by_cases hpd : p = H.d
  · haveI : P.LiesOver (span {(H.d : ℤ)}) := by rw [← hpd]; exact hpl
    have h3 := (inertia_d H P H.conj).mp h
    rw [h2] at h3
    rcases h3 with h3 | h3
    · exact cc_ne_one h3
    · have h4 := congrArg (fun g : φ.GG => ((g.1.1 : ℤˣ) : ℤ)) h3
      simp [Frame.cc, Frame.iod, c0] at h4
  · haveI := hpl
    have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
    exact Formalism.FrobeniusOrbits.Inertia.sqrt_fixed H.hyp.2.1 hd4 hp hpd P H.conj H.sqd_sq hcs h
end Formalism.HC.Der
