-- Prove2me | solution 1 for Formalism.GM.ProjS.fockForm_augLift_augLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:02.997464+00:00
-- url     : https://prove2.me/submissions/5eef0bcd-d182-4db7-a1be-c355652e5e9f

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_sum_right
import Theorems.Thm_Formalism_GM_ProjS_tieF_pow_pderiv
import Theorems.Thm_Formalism_GM_ProjS_tieF_pow_X_pow_mul
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_X_pow_mul
import Theorems.Thm_Formalism_GM_ProjS_pderiv_pow_X_pow_mul
import Theorems.Thm_Formalism_GM_ProjS_pderiv_of_free
import Theorems.Thm_Formalism_GM_ProjS_Fh_pow_u
import Theorems.Thm_Formalism_GM_ProjS_tieP_eq
import Theorems.Thm_Formalism_GM_ProjS_fh_P
import Theorems.Thm_Formalism_GM_ProjS_fockK_P_left
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc

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
private theorem mvPolynomial_pderiv_X_eq_zero_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  classical
  rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg h]
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
private theorem tieE_pow_apply_eq_sum_X_mul_X_pow_mul {q : ℕ} (W E : Fin q → σ) (j : ℕ) (g : MvPolynomial σ k) :
    (Formalism.GM.tieE W E ^ j) g = (∑ d, X (W d) * X (E d)) ^ j * g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' (Formalism.GM.tieE W E) j, Module.End.mul_apply, ih, Formalism.GM.tieE_apply',
      pow_succ' (∑ d, X (W d) * X (E d) : MvPolynomial σ k) j, mul_assoc]
private theorem tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow {q : ℕ} (W E : Fin q → σ) (o n z : ℕ) (g : MvPolynomial σ k) :
    Formalism.GM.tiePhi W E o n z g = ∑ l ∈ range (o + 1),
      (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + q + z - 1).choose l : k))) •
        (Formalism.GM.tieE W E ^ l) ((Formalism.GM.tieF W E ^ l) g) := by
  simp only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
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
    (_hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y') :
    M.fockK (M.tieP w e zv sv o n z y) (M.tieP w e zv sv o n z y') =
      (z.factorial : k) * M.fockK y (tiePhi w e o n z y') := by
  have hzz : ∀ c, w c ≠ zv ∧ e c ≠ zv := fun c => ⟨(hv.2.2.2.1 c).1, (hv.2.2.2.1 c).2.2.1⟩
  rw [fockK_P_left o n z y _ (fh_P (z := z) hv hr hy' hz')]
  have step1 : Formalism.GM.M.fockK (X zv ^ z * y) (Formalism.GM.M.tieP w e zv sv o n z y') =
      Formalism.GM.M.fockK (X zv ^ z * y) (Formalism.GM.tiePhi w e o n z (X zv ^ z * y')) := by
    rw [tieP_eq, tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, fockK_sum_right, fockK_sum_right]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [fockK_smul_right, fockK_smul_right, fockK_tieE_pow_right, fockK_tieE_pow_right,
      Fh_pow_u hv hz l]
  have hPX : Formalism.GM.tiePhi w e o n z (X zv ^ z * y') = X zv ^ z * Formalism.GM.tiePhi w e o n z y' := by
    rw [tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [tieF_pow_X_pow_mul w e zv hzz z y' l, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, mul_smul_comm,
      mul_left_comm]
  have hRs : pderiv zv (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero (fun d _ => ?_)
    rw [MvPolynomial.pderiv_mul, mvPolynomial_pderiv_X_eq_zero_of_ne (hzz d).1, mvPolynomial_pderiv_X_eq_zero_of_ne (hzz d).2, zero_mul, mul_zero, add_zero]
  have hPd : pderiv zv (Formalism.GM.tiePhi w e o n z y') = 0 := by
    rw [tiePhi_eq_sum_range_neg_one_pow_div_tieE_pow_tieF_pow, map_sum]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [Derivation.map_smul, tieE_pow_apply_eq_sum_X_mul_X_pow_mul, MvPolynomial.pderiv_mul, Derivation.leibniz_pow, hRs, smul_zero,
      smul_zero, zero_mul, zero_add, ← tieF_pow_pderiv,
      pderiv_of_free zv y' (fun m hm => (hz' m hm).1), map_zero, mul_zero, smul_zero]
  rw [step1, hPX, fockK_X_pow_mul, pderiv_pow_X_pow_mul zv _ hPd z, fockK_smul_right]
end Formalism.GM.ProjS
