-- Prove2me | solution 1 for Formalism.HC.Der.decompConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:07.687437+00:00
-- url     : https://prove2.me/submissions/5722f12a-2be5-42e7-ab17-b905da7b4792

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_exists_unit_crt
import Theorems.Thm_Formalism_HC_Der_tower_dvd_QSq
import Theorems.Thm_Formalism_HC_Der_cop_QSq_d
import Theorems.Thm_Formalism_HC_Der_ordCompl_d
import Theorems.Thm_Formalism_HC_Der_ps_d
import Theorems.Thm_Formalism_HC_Der_cc_not_mem_Psi
import Theorems.Thm_Formalism_HC_Der_inertia_d
import Theorems.Thm_Formalism_HC_Der_decomp_typeI
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_D7_inertia_d
import Theorems.Thm_Formalism_HC_D7_ordCompl_d
import Theorems.Thm_Formalism_HC_Der_cyc_isGalois
import Theorems.Thm_Formalism_HC_Der_exists_over
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
import Theorems.Thm_Formalism_HC_Der_tauN_frob
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
theorem _root_.solution : ∀ (l : ℕ), l.Prime → l ∣ H.condN →
    ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], H.conj ∉ MulAction.stabilizer _ P := by
  intro l hl hlN P _ _ hσ
  have h2 : H.gal H.conj = φ.cc := MulEquiv.apply_symm_apply _ _
  by_cases hlq : l ∣ H.QS * H.q
  · have h3 := decomp_typeI H l hl hlq P H.conj hσ
    rw [h2] at h3
    exact cc_not_mem_Psi h3
  have hld : l = H.d := by
    rcases (Nat.Prime.dvd_mul hl).mp hlN with h | h
    · exact absurd h hlq
    · exact (Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI hPd : P.LiesOver (span {(H.d : ℤ)}) := by rw [← hld]; infer_instance
  haveI := cyc_isGalois H.condN
  obtain ⟨Q, hQ, hQl, -, hF⟩ := exists_over (emb H) H.d P
  have hcd : Nat.Coprime H.d (H.QS * H.q) := (cop_QSq_d H).symm
  obtain ⟨uF, huF1, -⟩ := exists_unit_crt (cop_QSq_d H) H.d 1 hcd (Nat.coprime_one_left _)
  have hFrob : IsArithFrobAt ℤ (H.gal.symm (H.art uF)) P := by
    apply hF _ (tauN H.condN uF) ((gal_eq_art_iff H _ uF).mp (H.gal.apply_symm_apply _))
    apply tauN_frob H.condN H.d Q uF
    rw [ordCompl_d H]
    exact huF1
  obtain ⟨k, ρ, hρ, hconj⟩ := Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul H.d P _ H.conj hFrob hσ
  have hg : φ.cc = H.gal ρ * H.art uF ^ k := by
    rw [← h2, hconj, map_mul, map_pow, MulEquiv.apply_symm_apply]
  have hρ1 : (H.gal ρ).1.1 = 1 ∧ (H.gal ρ).2 = 1 := by
    rcases (inertia_d H P ρ).mp hρ with h | h <;> rw [h] <;> exact ⟨rfl, rfl⟩
  have hps := ps_d H uF huF1
  have h2N : 2 ^ (φ.e + 2) ∣ H.QS * H.q := tower_dvd_QSq H
  have hc2 : Nat.Coprime H.d (2 ^ (φ.e + 2)) := Nat.Coprime.coprime_dvd_right h2N hcd
  have hhv : φ.hH (H.art uF).2 = hcl φ.e (ZMod.unitOfCoprime H.d hc2) := by
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff]
    exact (huF1.of_dvd h2N).symm
  have hk2 : (H.art uF).2 ^ k = 1 := by
    have h0 := congrArg Prod.snd hg
    rw [Prod.snd_mul, Prod.pow_snd, hρ1.2, one_mul] at h0
    rw [← h0]
    rfl
  have hvk : ((ZMod.unitOfCoprime H.d hc2 ^ k : (ZMod (2 ^ (φ.e + 2)))ˣ) : HGrp φ.e) = 1 := by
    rw [QuotientGroup.mk_pow]
    show hcl φ.e (ZMod.unitOfCoprime H.d hc2) ^ k = 1
    rw [← hhv, ← map_pow, hk2, map_one]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_one_iff _ |>.mp hvk)
  have h16 : 16 ∣ 2 ^ (φ.e + 2) := by
    have h0 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h0]
    exact pow_dvd_pow 2 (by have := H.two_le_e; omega)
  have hfv : ZMod.castHom h16 (ZMod 16) ((ZMod.unitOfCoprime H.d hc2 : (ZMod (2 ^ (φ.e + 2)))ˣ) :
      ZMod (2 ^ (φ.e + 2))) = 7 := by
    rw [ZMod.coe_unitOfCoprime, map_natCast, ← ZMod.natCast_mod H.d 16, H.hyp.2.2.2.1]
    rfl
  have hpm : (7 : ZMod 16) ^ k = 1 ∨ (7 : ZMod 16) ^ k = -1 := by
    have h0 := congrArg (fun x : (ZMod (2 ^ (φ.e + 2)))ˣ =>
      ZMod.castHom h16 (ZMod 16) (x : ZMod (2 ^ (φ.e + 2)))) hn
    simp only [Units.val_pow_eq_pow_val, map_pow, hfv] at h0
    rcases Int.even_or_odd n with he | ho
    · left
      rw [he.neg_one_zpow, Units.val_one, map_one] at h0
      exact h0.symm
    · right
      rw [ho.neg_one_zpow, Units.val_neg, Units.val_one, map_neg, map_one] at h0
      exact h0.symm
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h0 := congrArg (fun g : φ.GG => g.1.1) hg
    simp only [Prod.fst_mul, Prod.pow_fst] at h0
    rw [hρ1.1, hps, one_mul, hj, ← two_mul, pow_mul, Int.units_sq, one_pow] at h0
    have h1 : (-1 : ℤˣ) = 1 := h0
    exact absurd (congrArg Units.val h1) (by norm_num)
  · have h7 : (7 : ZMod 16) ^ k = 7 := by
      rw [hj, pow_succ, pow_mul, (by decide : (7 : ZMod 16) ^ 2 = 1), one_pow, one_mul]
    rw [h7] at hpm
    revert hpm
    decide
end Formalism.HC.Der
