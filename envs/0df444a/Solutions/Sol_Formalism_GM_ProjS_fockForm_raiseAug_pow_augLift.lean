-- Prove2me | solution 1 for Formalism.GM.ProjS.fockForm_raiseAug_pow_augLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:11.968871+00:00
-- url     : https://prove2.me/submissions/ad670493-1b7f-49da-b2b0-8b91cacb7b26

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_symm
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_left
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_zero_right
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow
import Theorems.Thm_Formalism_GM_ProjS_tieEh_eq
import Theorems.Thm_Formalism_GM_ProjS_tv_w
import Theorems.Thm_Formalism_GM_ProjS_tv_e
import Theorems.Thm_Formalism_GM_ProjS_tv_we
import Theorems.Thm_Formalism_GM_ProjS_eig_P
import Theorems.Thm_Formalism_GM_ProjS_tieP_eq
import Theorems.Thm_Formalism_GM_ProjS_fh_P
import Theorems.Thm_Formalism_GM_ProjS_fockForm_augLift_augLift
import Theorems.Thm_Formalism_GM_F_pow_E_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
section
variable {s : ℕ} {w e : Fin s → σ}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
section
variable {o n z : ℕ} {y : MvPolynomial σ k}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
private theorem fockK_tieE_pow_tieE_pow_eq_ite {q : ℕ} {W E : Fin q → σ} (hW : Function.Injective W)
    (hE : Function.Injective E) (hWE : ∀ c d, W c ≠ E d) (a b N0 : ℕ) (hN : a + b + q = N0 + 1)
    (u u' : MvPolynomial σ k) (hu' : Formalism.GM.tieF W E u' = 0) (hWu' : eulL W u' = (a : k) • u')
    (hEu' : eulL E u' = (b : k) • u') (hu : Formalism.GM.tieF W E u = 0) (i l : ℕ) (hil : i ≤ l) :
    Formalism.GM.M.fockK ((Formalism.GM.tieE W E ^ i) u) ((Formalism.GM.tieE W E ^ l) u') =
      if i = l then ((i.factorial * (N0 + i).descFactorial i : ℕ) : k) * Formalism.GM.M.fockK u u' else 0 := by
  rw [fockK_tieE_pow, Formalism.GM.F_pow_E_pow hW hE hWE u' a b N0 (by rw [← eulL_apply W u']; exact hWu')
    (by rw [← eulL_apply E u']; exact hEu') hu' hN i l, fockK_smul_right]
  split_ifs with h
  · subst h
    rw [Nat.sub_self, pow_zero, Module.End.one_apply, Nat.descFactorial_self]
  · obtain ⟨m, hm⟩ : ∃ m, l - i = m + 1 := ⟨l - i - 1, by omega⟩
    rw [hm, pow_succ' (Formalism.GM.tieE W E) m, Module.End.mul_apply, fockK_symm u, fockK_tieE, hu,
      fockK_zero_right, mul_zero]
end Formalism.GM.ProjS
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    (j j' : ℕ) :
    M.fockK ((((j.factorial : k))⁻¹) • ((M.tieEh w e zv sv) ^ j) (M.tieP w e zv sv o n z y))
        ((((j'.factorial : k))⁻¹) • ((M.tieEh w e zv sv) ^ j') (M.tieP w e zv sv o n z y')) =
      if j = j' then (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k) *
        M.fockK y (tiePhi w e o n z y') else 0 := by
  have hw' := tv_w hv
  have he' := tv_e hv
  have hd := tv_we hv
  have hL := fh_P (z := z) hv hr hy hz
  have hL' := fh_P (z := z) hv hr hy' hz'
  have hE : eulL (Fin.cons zv w : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y) =
        ((o + z : ℕ) : k) • Formalism.GM.M.tieP w e zv sv o n z y ∧
      eulL (Fin.cons sv e : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y) =
        (n : k) • Formalism.GM.M.tieP w e zv sv o n z y := by
    rw [tieP_eq]
    exact eig_P (z := z) hv hy hz _
  have hE' : eulL (Fin.cons zv w : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y') =
        ((o + z : ℕ) : k) • Formalism.GM.M.tieP w e zv sv o n z y' ∧
      eulL (Fin.cons sv e : Fin (r + 1) → σ) (Formalism.GM.M.tieP w e zv sv o n z y') =
        (n : k) • Formalism.GM.M.tieP w e zv sv o n z y' := by
    rw [tieP_eq]
    exact eig_P (z := z) hv hy' hz' _
  have hN : (o + z) + n + (r + 1) = (o + z + n + r) + 1 := by omega
  rw [tieEh_eq, fockK_smul_left, fockK_smul_right]
  by_cases h : j = j'
  · subst j'
    rw [fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL' hE'.1 hE'.2 hL j j le_rfl,
      if_pos rfl, if_pos rfl, fockForm_augLift_augLift (z := z) hv hr hy hy' hz hz']
    have h1 : o + n + r + z + 1 + j - 1 = o + z + n + r + j := by omega
    have hf : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have e1 : (j.factorial : k)⁻¹ * (j.factorial : k) = 1 := inv_mul_cancel₀ hf
    rw [h1, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    linear_combination (((j.factorial : k)⁻¹ * (j.factorial : k) + 1) *
      (((o + z + n + r + j).choose j : ℕ) : k) * (z.factorial : k) *
      Formalism.GM.M.fockK y (Formalism.GM.tiePhi w e o n z y')) * e1
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL' hE'.1 hE'.2 hL j j' hlt.le,
        if_neg h, mul_zero, mul_zero]
    · rw [fockK_symm, fockK_tieE_pow_tieE_pow_eq_ite hw' he' hd (o + z) n (o + z + n + r) hN _ _ hL hE.1 hE.2 hL'
        j' j hgt.le, if_neg (Ne.symm h), mul_zero, mul_zero]
end Formalism.GM.ProjS
