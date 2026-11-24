-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.term_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:47.998815+00:00
-- url     : https://prove2.me/submissions/966c0e0b-b203-4081-9468-2353fdd19ed1

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vchoose_le
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vfact_split
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_v_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vW_ge
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_deg_le_total
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_kap_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hk : ∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k))
    (hW : δv δ (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) - j)
    (hY : δv δ (Fin.last (N + 1)) = LL.total - (j - a))
    (d1 d2 : ℕ) (hd1 : padicValNat p a.factorial ≤ padicValNat p d1) (hd1' : d1 ≠ 0)
    (hd2 : padicValNat p a'.factorial ≤ padicValNat p d2) (hd2' : d2 ≠ 0) :
    -(kap N r B : ℤ) + ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))) +
      ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ))) -
      (padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) +
      (padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) : ℤ) ≤ 0 := by
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  have hoS : o ≤ S := deg_le_total LL (Fin.last N)
  set T := S + o + r
  have hjo : j ≤ o := hj

  have nz1 : j.choose a ≠ 0 := (Nat.choose_pos ha).ne'
  have nz2 : j.choose a' ≠ 0 := (Nat.choose_pos ha').ne'
  have nzW : (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have vN : padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
      ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) =
      padicValNat p (j.choose a) + padicValNat p (j.choose a') + padicValNat p d1 + padicValNat p d2 +
        padicValNat p a'.factorial + padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) := by
    rw [padicValNat.mul (by positivity) nzW, padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (by positivity) hd2', padicValNat.mul (by positivity) hd1',
      padicValNat.mul nz1 nz2]

  have nzC : o.choose j ≠ 0 := (Nat.choose_pos hjo).ne'
  have nzD : (∏ i, (LL.deg i).factorial) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have vD : padicValNat p (o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial) =
      padicValNat p (o.choose j) + 2 * padicValNat p j.factorial + padicValNat p S.factorial +
        ∑ i, padicValNat p (LL.deg i).factorial := by
    rw [padicValNat.mul (by positivity) nzD, padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul nzC (by positivity), padicValNat.pow,
      v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have vDn : ∑ i, padicValNat p (LL.deg i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial + padicValNat p o.factorial := by
    rw [Fin.sum_univ_castSucc]

  have hTδ : ∀ i, δv δ i ≤ T := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hY]; omega
    | cast i =>
      induction i using Fin.lastCases with
      | last => rw [hW]; omega
      | cast k => rw [hk k]; have := deg_le_total LL (Fin.castSucc k); omega
  have hlog : Nat.log p T ≤ B := hB
  have vW := vW_ge (p := p) δ hlog hTδ
  have vS : ∑ i, padicValNat p (δv δ i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial + padicValNat p (o - j).factorial +
        padicValNat p (S - (j - a)).factorial := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hW, hY]
    simp only [hk]

  have F1 : padicValNat p j.factorial ≤ padicValNat p a.factorial + padicValNat p (j - a).factorial + B := by
    have := vfact_split (p := p) (a := a) (b := j - a) (T := T) (by omega) hlog
    rwa [show a + (j - a) = j by omega] at this
  have F2 : padicValNat p j.factorial ≤ padicValNat p a'.factorial + padicValNat p (j - a').factorial + B := by
    have := vfact_split (p := p) (a := a') (b := j - a') (T := T) (by omega) hlog
    rwa [show a' + (j - a') = j by omega] at this
  have F3 : padicValNat p o.factorial ≤ padicValNat p (o - j).factorial + padicValNat p j.factorial + B := by
    have := vfact_split (p := p) (a := o - j) (b := j) (T := T) (by omega) hlog
    rwa [show o - j + j = o by omega] at this
  have F4 : padicValNat p S.factorial ≤ padicValNat p (S - (j - a)).factorial + padicValNat p (j - a).factorial + B := by
    have := vfact_split (p := p) (a := S - (j - a)) (b := j - a) (T := T) (by omega) hlog
    rwa [show S - (j - a) + (j - a) = S by omega] at this
  have F5 : padicValNat p (o.choose j) ≤ B := vchoose_le (show o ≤ T by omega) hlog
  have hk' := kap_ge N r B hr
  rw [vN, vD, vDn]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  have hk'' : (((N + 4) * (r * B) + 6 * B : ℕ) : ℤ) ≤ (kap N r B : ℤ) := by exact_mod_cast hk'
  push_cast at hk''
  have vW' : (∑ i, (padicValNat p (δv δ i).factorial : ℤ)) ≤
      (padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) + (N + 2) * (r * B) := by
    exact_mod_cast vW
  have vS' : (∑ i, (padicValNat p (δv δ i).factorial : ℤ)) =
      (∑ k : Fin N, (padicValNat p (LL.deg (Fin.castSucc k)).factorial : ℤ)) + (padicValNat p (o - j).factorial : ℤ) +
        (padicValNat p (S - (j - a)).factorial : ℤ) := by exact_mod_cast vS
  have F1' : (padicValNat p j.factorial : ℤ) ≤ padicValNat p a.factorial + padicValNat p (j - a).factorial + B := by
    exact_mod_cast F1
  have F2' : (padicValNat p j.factorial : ℤ) ≤ padicValNat p a'.factorial + padicValNat p (j - a').factorial + B := by
    exact_mod_cast F2
  have F3' : (padicValNat p o.factorial : ℤ) ≤ padicValNat p (o - j).factorial + padicValNat p j.factorial + B := by
    exact_mod_cast F3
  have F4' : (padicValNat p S.factorial : ℤ) ≤ padicValNat p (S - (j - a)).factorial + padicValNat p (j - a).factorial + B := by
    exact_mod_cast F4
  have F5' : (padicValNat p (o.choose j) : ℤ) ≤ B := by exact_mod_cast F5
  have hd1z : (padicValNat p a.factorial : ℤ) ≤ padicValNat p d1 := by exact_mod_cast hd1
  have hd2z : (padicValNat p a'.factorial : ℤ) ≤ padicValNat p d2 := by exact_mod_cast hd2
  have c1 : (0 : ℤ) ≤ padicValNat p (j.choose a) := by positivity
  have c2 : (0 : ℤ) ≤ padicValNat p (j.choose a') := by positivity
  linarith
end Formalism.GM.gammaIntegralityLemmas
