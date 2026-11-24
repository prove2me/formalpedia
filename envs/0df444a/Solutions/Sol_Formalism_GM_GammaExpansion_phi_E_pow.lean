-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.phi_E_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:10.43694+00:00
-- url     : https://prove2.me/submissions/140dfda1-dc7c-4637-b0f0-622cf3227a86

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_E_swap
import Theorems.Thm_Formalism_GM_GammaExpansion_phi_E_step
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


section
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {r : ℕ} (w e : Fin r → σ)
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
private theorem EW_E_lemma_8 (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d) (α : k) (Y : MvPolynomial σ k)
    (h : EW w Y = α • Y) : EW w (tieE w e Y) = (α + 1) • tieE w e Y := by
  classical
  have hdW : ∀ c, pderiv (w c) (∑ c', X (w c') * X (e c') : MvPolynomial σ k) = X (e c) := by
    intro c
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, hw.eq_iff, fun a b => (hwe a b).symm]
  have hEW : EW w Y = ∑ c, X (w c) * pderiv (w c) Y := rfl
  simp only [tieE, LinearMap.mulLeft_apply, EW, Derivation.leibniz, smul_eq_mul, hdW, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ c, X (w c) * ((∑ c', X (w c') * X (e c')) * pderiv (w c) Y) =
      (∑ c', X (w c') * X (e c')) * (α • Y) := by
    rw [← h, hEW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∑ c, X (w c) * (Y * X (e c)) = (∑ c', X (w c') * X (e c')) * Y := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [h1, h2, add_smul, one_smul, mul_smul_comm]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Polynomial Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
end
section
variable (p : ℕ) [Fact p.Prime]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM
open MvPolynomial Finset
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) :
    ∀ (s o n z : ℕ) (Z : MvPolynomial σ k), s ≤ o → s ≤ n →
      EW w Z = ((o - s : ℕ) : k) • Z → EW e Z = ((n - s : ℕ) : k) • Z →
      tiePhi w e o n z ((tieE w e ^ s) Z) =
        (∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k))) •
          (tieE w e ^ s) (tiePhi w e (o - s) (n - s) (z + s) Z) := by
  intro s
  induction s with
  | zero => intro o n z Z _ _ _ _; simp
  | succ s ih =>
    intro o n z Z hso hsn hW hE
    have hW' : EW w (tieE w e Z) = ((o - s : ℕ) : k) • tieE w e Z := by
      rw [EW_E_lemma_8 hw hwe _ Z hW]
      congr 1
      rw [show o - s = o - (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
    have hE' : EW e (tieE w e Z) = ((n - s : ℕ) : k) • tieE w e Z := by
      rw [E_swap, EW_E_lemma_8 he (fun c d => (hwe d c).symm) _ Z hE]
      congr 1
      rw [show n - s = n - (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
    have hE1 : (tieE w e ^ (s + 1)) Z = (tieE w e ^ s) (tieE w e Z) := by rw [pow_succ] <;> rfl
    rw [hE1, ih o n z (tieE w e Z) (by omega) (by omega) hW' hE']
    have ho : o - s = (o - (s + 1)) + 1 := by omega
    have hn : n - s = (n - (s + 1)) + 1 := by omega
    rw [ho, hn, phi_E_step hw he hwe (o - (s + 1)) (n - (s + 1)) (z + s) Z hW hE]
    rw [map_smul, smul_smul, Finset.prod_range_succ]
    have hE2 : (tieE w e ^ s) (tieE w e (tiePhi w e (o - (s + 1)) (n - (s + 1)) (z + s + 1) Z)) =
        (tieE w e ^ (s + 1)) (tiePhi w e (o - (s + 1)) (n - (s + 1)) (z + (s + 1)) Z) := by
      rw [← add_assoc]
      rw [pow_succ] <;> rfl
    rw [hE2]
    congr 2
    have h3 : o - (s + 1) + (n - (s + 1)) + r + (z + s) + 1 = o + n + r + z - 1 - s := by omega
    rw [h3]
    push_cast <;> ring
end Formalism.GM.GammaExpansion
