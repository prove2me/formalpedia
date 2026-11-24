-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_E_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:10.126423+00:00
-- url     : https://prove2.me/submissions/0ca8ca8e-9628-4d90-a424-22ec2ef2e049

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaD
import Theorems.Thm_Formalism_UG_P_fIwasawa_E_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (ρ : Fin n) (z : Fin n → L) (c : L)
    (hz : ∀ t, z t ≠ 0 → ρ < t ∧ t < Fin.rev ρ) (w : Fin n → L) (hwρ : w ρ = 0)
    (hw : ∀ t, ρ < t → t < Fin.rev ρ → w t = 0) :
    fIwasawaE σ (Pi.single (Fin.rev ρ) 1) z c *ᵥ w = w := by
  have h1 : fIwasawaH σ (Pi.single (Fin.rev ρ) 1) w = 0 := by
    unfold fIwasawaH
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = ρ
    · subst hj; rw [hwρ, mul_zero]
    · rw [Pi.single_eq_of_ne (by rwa [Ne, Fin.rev_inj]), map_zero, zero_mul]
  have h2 : fIwasawaH σ z w = 0 := by
    unfold fIwasawaH
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hzj : z (Fin.rev j) = 0
    · rw [hzj, map_zero, zero_mul]
    · obtain ⟨ha, hb⟩ := hz _ hzj
      have hj1 : ρ < j := by simpa using Fin.rev_lt_rev.1 hb
      have hj2 : j < Fin.rev ρ := by simpa using Fin.rev_lt_rev.2 ha
      rw [hw j hj1 hj2, mul_zero]
  rw [fIwasawa_E_mulVec, h1, h2]
  simp
end Formalism.UG.P
