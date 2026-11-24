-- Prove2me | solution 1 for Formalism.HC.Der.exists_art_iod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:02.357955+00:00
-- url     : https://prove2.me/submissions/863bbbc9-bbb2-4fe3-b802-c8adeddc7c52

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_exists_unit_crt
import Theorems.Thm_Formalism_HC_Der_cop_QSq_d
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_HC_Der_tauN_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
private theorem art_snd_lemma (u : (ZMod H.condN)ˣ) :
    (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hz := Cond.z_spec H.condN
  have hx : IsPrimitiveRoot (Cond.z H.condN ^ (H.QS * H.q)) H.d :=
    hz.pow (Nat.pos_of_ne_zero (NeZero.ne H.condN)) rfl
  have hg2 : Cond.gs H.d hx.pow_eq_one ^ 2 = -(H.d : Cond.Cyc H.condN) := Cond.gs_sq hd4 hx
  have hy2 : (emb H H.sqd) ^ 2 = -(H.d : Cond.Cyc H.condN) := by
    rw [← map_pow, H.sqd_sq, map_neg, map_natCast]
  have hy0 : emb H H.sqd ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hy2
    have h0 : (H.d : Cond.Cyc H.condN) = 0 := by linear_combination hy2
    exact H.hyp.2.1.ne_zero (by exact_mod_cast h0)
  have hτx : (tauN H.condN u) (Cond.z H.condN ^ (H.QS * H.q)) =
      (Cond.z H.condN ^ (H.QS * H.q)) ^ (u : ZMod H.condN).val :=
    tauN_root H.condN u _ (by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow])
  have hcopv : Nat.Coprime (u : ZMod H.condN).val H.d :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left H.d (H.QS * H.q)) (ZMod.val_coe_unit_coprime u)
  have hτg : (tauN H.condN u) (Cond.gs H.d hx.pow_eq_one) =
      ((jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d : ℤ) : Cond.Cyc H.condN) *
        Cond.gs H.d hx.pow_eq_one :=
    Formalism.HC.D7.gs_act hx.pow_eq_one
      ((tauN H.condN u : Cond.Cyc H.condN ≃ₐ[ℚ] Cond.Cyc H.condN) : Cond.Cyc H.condN →+* Cond.Cyc H.condN)
      _ hτx hcopv
  have hτy : (tauN H.condN u) (emb H H.sqd) =
      ((jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d : ℤ) : Cond.Cyc H.condN) * emb H H.sqd := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy2.trans hg2.symm) with h | h
    · rw [h]
      exact hτg
    · rw [h, map_neg, hτg, mul_neg]
  have hσ := H.gal_sqd (H.gal.symm (H.art u))
  rw [MulEquiv.apply_symm_apply] at hσ
  have h2 := emb_art H u H.sqd
  rw [hσ, map_mul, map_intCast, hτy] at h2
  have h3 := mul_right_cancel₀ hy0 h2
  exact_mod_cast h3
end Formalism.HC.Der
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD H.QS * H.q] ∧ H.art u = φ.iod := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have hd4 : H.d % 4 = 3 := by have := H.hyp.2.2.2.1; omega
  have hd1 : 1 ≤ H.d := H.hyp.2.1.one_lt.le
  have hcop : Nat.Coprime (H.d - 1) H.d :=
    ((Nat.Prime.coprime_iff_not_dvd H.hyp.2.1).mpr
      (Nat.not_dvd_of_pos_of_lt (by have := H.hyp.2.1.two_le; omega) (by omega))).symm
  obtain ⟨u, hu1, hu2⟩ := exists_unit_crt (cop_QSq_d H) 1 (H.d - 1) (Nat.coprime_one_left _) hcop
  refine ⟨u, hu1, ?_⟩
  have hdv : H.d ∣ (u : ZMod H.condN).val + 1 := by
    have h0 : ((u : ZMod H.condN).val + 1) % H.d = (H.d - 1 + 1) % H.d := hu2.add_right 1
    rw [Nat.sub_add_cancel hd1, Nat.mod_self] at h0
    exact Nat.dvd_of_mod_eq_zero h0
  have hv : ((u : ZMod H.condN).val : ℤ) % (H.d : ℤ) = (-1 : ℤ) % (H.d : ℤ) := by
    have h0 : (H.d : ℤ) ∣ ((u : ZMod H.condN).val : ℤ) + 1 := by exact_mod_cast hdv
    have h1 : Int.ModEq (H.d : ℤ) ((u : ZMod H.condN).val : ℤ) (-1) := by
      apply Int.modEq_iff_dvd.mpr
      rw [show (-1 : ℤ) - ((u : ZMod H.condN).val : ℤ) = -(((u : ZMod H.condN).val : ℤ) + 1) by ring]
      exact h0.neg_right
    exact h1
  have hJ : jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d = -1 := by
    rw [jacobiSym.mod_left, hv, ← jacobiSym.mod_left,
      jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hd4]
  rcases H.art_d u hu1 with h | h
  · exfalso
    have h0 := art_snd_lemma H u
    rw [h, hJ] at h0
    norm_num at h0
  · exact h
end Formalism.HC.Der
