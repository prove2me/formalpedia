-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_vLa_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:55.240526+00:00
-- url     : https://prove2.me/submissions/610ab142-648f-4904-ae61-6d761ddc49c9

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_resCharOf_prime
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_pow
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_coprime
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) :
    vLa la ((N : ℕ) : K) = (padicValNat (resCharOf la) N * ramOverZ la : ℕ) := by
  have hp := resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hp⟩
  obtain ⟨n', hn'⟩ : resCharOf la ^ padicValNat (resCharOf la) N ∣ N := pow_padicValNat_dvd
  have hndvd : ¬ resCharOf la ∣ n' := by
    rintro ⟨b, rfl⟩
    have hd : resCharOf la ^ (padicValNat (resCharOf la) N + 1) ∣
        resCharOf la ^ padicValNat (resCharOf la) N * (resCharOf la * b) := ⟨b, by ring⟩
    rw [← hn'] at hd
    exact pow_succ_padicValNat_not_dvd (p := resCharOf la) hN hd
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hN (by simpa using hn')
  have hK : ((N : ℕ) : K) = ((resCharOf la : ℕ) : K) ^ padicValNat (resCharOf la) N * ((n' : ℕ) : K) := by
    conv_lhs => rw [hn']
    push_cast
    ring
  have hp0 : ((resCharOf la : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hn0' : ((n' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [hK, crv_vLa_mul la (pow_ne_zero _ hp0) hn0', crv_vLa_pow la hp0, crv_vLa_coprime la hndvd,
    crv_vLa_char]
  push_cast
  ring
end Formalism.L2.Pj.Crude
