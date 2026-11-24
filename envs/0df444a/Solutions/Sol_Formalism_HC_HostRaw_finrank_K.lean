-- Prove2me | solution 1 for Formalism.HC.HostRaw.finrank_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:47.154165+00:00
-- url     : https://prove2.me/submissions/d29f4aca-a6c5-4e3a-a598-c60680d0e221

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : Module.finrank ℚ H.K = 2 := by
  have hint : IsIntegral ℚ H.sqd := Algebra.IsIntegral.isIntegral _
  unfold HostRaw.K
  rw [IntermediateField.adjoin.finrank hint]
  have hp0 : (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_add_C_ne_zero (by norm_num) _
  have hpa : Polynomial.aeval H.sqd (Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ)) = 0 := by
    simp [H.sqd_sq]
  have hle : (minpoly ℚ H.sqd).natDegree ≤ 2 := by
    have hd := minpoly.degree_le_of_ne_zero ℚ H.sqd hp0 hpa
    rw [Polynomial.degree_X_pow_add_C (by norm_num)] at hd
    exact Polynomial.natDegree_le_of_degree_le hd
  have hpos := minpoly.natDegree_pos hint
  have hne1 : (minpoly ℚ H.sqd).natDegree ≠ 1 := by
    intro h1
    obtain ⟨r, hr⟩ := minpoly.natDegree_eq_one_iff.1 h1
    have hsq := H.sqd_sq
    rw [← hr] at hsq
    have hr2 : r ^ 2 = -(H.d : ℚ) := by
      apply (algebraMap ℚ H.E).injective
      rw [map_pow, hsq, map_neg, map_natCast]
    have h0 : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
    have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
    linarith
  omega
end Formalism.HC.HostRaw
