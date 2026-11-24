-- Prove2me | solution 1 for Formalism.HC.HostRaw.art_eq_one_of_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:11.99979+00:00
-- url     : https://prove2.me/submissions/e58b9e9f-0e7d-4314-b2a9-9cbdc7083ae8

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_Der_exists_unit_modEq
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QSd_q
import Theorems.Thm_Formalism_HC_HostRaw_q_dvd_condN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d])
    (hj : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.q = 1) : H.art u = 1 := by
  have : Fact H.q.Prime := ⟨H.q_prime⟩
  have hc := H.coprime_QSd_q
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  have hcop : Nat.Coprime (u : ZMod H.condN).val H.q := (ZMod.val_coe_unit_coprime u).coprime_dvd_right H.q_dvd_condN
  have hr2 : (u : ZMod H.condN).val ≡ r.val * r.val [MOD H.q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast at hr ⊢
    rw [hr, ZMod.natCast_zmod_val]
  have hrc : Nat.Coprime r.val H.q := Nat.Coprime.coprime_mul_left (k := r.val) (hr2.gcd_eq.symm.trans hcop)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hc 1 r.val
  have hN : H.QS * H.d * H.q = H.condN := mul_right_comm _ _ _
  obtain ⟨v, hv⟩ := exists_unit_modEq (dvd_refl H.condN) n
    (hN ▸ Nat.Coprime.mul_right (hn1.gcd_eq.trans (Nat.coprime_one_left _)) (hn2.gcd_eq.trans hrc))
  have hv1 : (v : ZMod H.condN).val ≡ 1 [MOD H.QS * H.d] := (hv.of_dvd ⟨H.q, hN.symm⟩).trans hn1
  have huv : u = v ^ 2 := by
    have h1 : (u : ZMod H.condN).val ≡ n * n [MOD H.condN] := by
      have h2 := (Nat.modEq_and_modEq_iff_modEq_mul hc).1
        ⟨hu.trans (hn1.mul hn1).symm, hr2.trans (hn2.mul hn2).symm⟩
      rwa [hN] at h2
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (u : ZMod H.condN), (ZMod.natCast_eq_natCast_iff _ _ _).2 h1,
      Units.val_pow_eq_pow_val, ← ZMod.natCast_zmod_val (v : ZMod H.condN), (ZMod.natCast_eq_natCast_iff _ _ _).2 hv]
    push_cast
    ring
  rw [huv, map_pow, H.art_q v hv1]
end Formalism.HC.HostRaw
