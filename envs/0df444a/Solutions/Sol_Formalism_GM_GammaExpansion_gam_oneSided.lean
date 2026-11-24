-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.gam_oneSided
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:10.47743+00:00
-- url     : https://prove2.me/submissions/a209a24b-98fd-4040-8f2a-efab8319a1e1

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_comm
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_smul_left
import Theorems.Thm_Formalism_GM_GammaExpansion_tieE_pow_apply
import Theorems.Thm_Formalism_GM_GammaExpansion_phi_E_pow
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mono
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_const
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_congr
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_sum
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_choose_prod
import Theorems.Thm_Formalism_GM_GammaExpansion_coef_PD
import Theorems.Thm_Formalism_GM_GammaExpansion_exists_X_pow_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_quot_mem_pol
import Theorems.Thm_Formalism_GM_GammaExpansion_Z_biHom
import Theorems.Thm_Formalism_GM_GammaExpansion_q_etaDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_fock_expand
import Theorems.Thm_Formalism_GM_GammaExpansion_alg_step
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
import Theorems.Thm_Formalism_GM_euler_e_of_biHom
import Theorems.Thm_Formalism_GM_euler_w_of_biHom
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



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (N r : ℕ) (LL : M.Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r) (hvec : LL.vec (Fin.last N) = true)
    (hf : f ∈ M.Pol p r LL) (hord : ∀ m ∈ f.support, e ≤ m (Fin.last N, ρ)) (heo : e ≤ LL.deg (Fin.last N)) :
    IsPD LL.total (LL.total + LL.deg (Fin.last N) - e) (fun n => M.tieGam p LL ρ z n f f') := by
  set S := LL.total with hS
  set o := LL.deg (Fin.last N) with ho
  have hoS : o ≤ S := by
    simp only [hS, ho, M.Letters.total]
    exact single_le_sum (f := LL.deg) (fun _ _ => Nat.zero_le _) (mem_univ _)
  obtain ⟨h, hfh, hh⟩ := exists_X_pow_mul (Fin.last N, ρ) e f hord
  have hhP := quot_mem_pol p LL ρ e f h hf hh
  set q := aeval (M.freezeSub p LL ρ) h with hq
  set y := aeval (M.freezeSub p LL ρ) f' with hy
  set w : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.castSucc (Fin.last N), c) with hwdef
  set eη : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.last (N + 1), c) with hedef
  have hw : Function.Injective w := fun a b hab => by simpa [w] using hab
  have he : Function.Injective eη := fun a b hab => by simpa [eη] using hab
  have hwe : ∀ c d, w c ≠ eη d := fun c d h => by
    simp only [w, eη, Prod.mk.injEq] at h; exact (Fin.castSucc_lt_last _).ne h.1
  have hK : ∀ s ∈ q.support, s (eη ρ) ≤ S - e := q_etaDeg p LL ρ e heo h hhP
  have hsub : M.freezeSub p LL ρ (Fin.last N, ρ) = ∑ c, X (w c) * X (eη c) := by
    simp [M.freezeSub, hvec, w, eη]
  have hfreeze : ∀ n, M.freeze p LL ρ n f = (tieE w eη ^ e) (X (eη ρ) ^ (n - S) * q) := by
    intro n
    rw [tieE_pow_apply]
    unfold M.freeze
    rw [hfh, map_mul, map_pow, aeval_X, hsub]
    ring
  have hfreeze' : ∀ n, M.freeze p LL ρ n f' = X (eη ρ) ^ (n - S) * y := fun n => rfl
  have hphi : ∀ n, M.tiePhiAt p (LL.snoc n) (Fin.castSucc (Fin.last N)) (Fin.last (N + 1)) z =
      tiePhi w eη o n z := by
    intro n; simp [M.tiePhiAt, M.Letters.snoc, w, eη, o]
  set T : ℕ → ℕ → ℕ → MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p] := fun j i t =>
    X (w ρ) ^ i * (∑ c, X (w c) * X (eη c)) ^ (e + j - i) *
      (tieF w eη ^ j) (X (eη ρ) ^ (i + t) * (Dp (eη ρ) ^ t) q) with hT
  set Den : ℚ_[p] := ((S.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p]) with hDen
  have key : IsPD S (S + o - e) (fun n => ∑ j ∈ range (o - e + 1),
      ((((o + n + r + z - 1).choose o : ℕ) : ℚ_[p]) *
        (∏ i ∈ range e, (((z : ℚ_[p]) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : ℚ_[p]))) *
          cph ℚ_[p] ((o - e) + (n - e) + r + (z + e) - 1) j) *
        ∑ i ∈ range (e + j + 1), ∑ t ∈ range (S - e + 1),
          (((((n - S).choose i * (n - S - i).choose t : ℕ)) : ℚ_[p]) *
            (((e + j).descFactorial i : ℚ_[p]) / ((i + t).factorial : ℚ_[p]) * (M.fock p y (T j i t) / Den)))) := by
    apply IsPD.sum
    intro j hj
    have hj' : j ≤ o - e := by simpa [Nat.lt_succ_iff] using hj
    refine ((coef_PD o r z e j S hr (by omega) hoS).mul (d' := e + j + (S - e)) ?_).mono (by omega)
    apply IsPD.sum
    intro i hi
    apply IsPD.sum
    intro t ht
    have hi' : i ≤ e + j := by simpa [Nat.lt_succ_iff] using hi
    have ht' : t ≤ S - e := by simpa [Nat.lt_succ_iff] using ht
    exact ((IsPD.choose_prod S i t).mul (IsPD.const S 0 _)).mono (by omega)
  refine key.congr (fun n hn => ?_)
  have hen : e ≤ n := by omega
  have hB := Z_biHom p LL ρ e heo h hhP (n - S)
  rw [show n - S + (LL.total - e) = n - e by omega] at hB
  have hEW := euler_w_of_biHom w eη hB
  have hEH := euler_e_of_biHom w eη hB
  unfold M.tieGam
  rw [hphi n, hfreeze n, hfreeze' n, phi_E_pow hw he hwe e o n z _ heo hen hEW hEH, fock_smul_left, fock_comm,
    fock_expand p he hwe ρ q y (S - e) hK (o - e) (n - e) (z + e) e (n - S)]
  have hm : (((n - S).factorial : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD : Den ≠ 0 := by
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) ?_
    exact prod_ne_zero_iff.mpr (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [show ((((n - S).factorial * S.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p])) =
    (((n - S).factorial : ℕ) : ℚ_[p]) * Den by rw [hDen, Nat.cast_mul]; ring]
  rw [mul_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro j _
  refine alg_step _ _ _ _ _ _ _ hm hD ?_
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  rw [sum_div]
  apply sum_congr rfl
  intro t _
  simp only [hT]
  ring
end Formalism.GM.GammaExpansion
