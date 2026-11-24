-- Prove2me | solution 1 for Formalism.HC.Der.kc_iod_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:37.283522+00:00
-- url     : https://prove2.me/submissions/e613cd86-f464-4863-8120-d40b41a94c0c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcEqOfPowEqOne
import Theorems.Thm_Formalism_HC_Der_kc_eq_of_pow_eq_one
import Theorems.Thm_Formalism_HC_Der_kc_no_root_d
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
variable (C : HostCore H)
include C
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ = φ.iod) (x : H.E) (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : σ x = x := by
  obtain ⟨n, hn, hxn⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hxn⟩
  have hmpos : 0 < orderOf x := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hd : ¬ H.d ∣ orderOf x := by
    rintro ⟨k, hk⟩
    exact kc_no_root_d H C _ (hprim.pow hmpos (by rw [hk, mul_comm]))
  have : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(H.d : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  have hin := (C.inertia_d P σ).mpr (Or.inr hσ)
  have hint : IsIntegral ℤ x := hprim.isIntegral hmpos
  let X : 𝓞 H.E := ⟨x, hint⟩
  have hX : X ^ orderOf x = 1 := by
    apply RingOfIntegers.ext
    have : ((X ^ orderOf x : 𝓞 H.E) : H.E) = (X : H.E) ^ orderOf x := by push_cast; rfl
    rw [this]
    exact hprim.pow_eq_one
  have hX' : (σ • X) ^ orderOf x = 1 := by rw [← smul_pow', hX, smul_one]
  have hm : ((orderOf x : ℕ) : 𝓞 H.E) ∉ P := by
    intro h0
    have h1 := (odd_intCast_mem_iff H.d P ((orderOf x : ℕ) : ℤ)).mp (by exact_mod_cast h0)
    exact hd (by exact_mod_cast h1)
  have := kc_eq_of_pow_eq_one P hm hX' hX (hin X)
  exact congrArg (fun y : 𝓞 H.E => (y : H.E)) this
end Formalism.HC.Der
