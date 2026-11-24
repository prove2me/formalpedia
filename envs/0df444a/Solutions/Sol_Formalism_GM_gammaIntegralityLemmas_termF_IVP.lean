-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.termF_IVP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:38.968049+00:00
-- url     : https://prove2.me/submissions/7b87de66-fc55-4d4c-bf57-55ec84ddb0ab

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mono
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_smul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_choose_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vdesc_ge
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_zero_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_pow_monomial_lt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_mul
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_X_pow_mul_monomial
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_Dop_term
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_norm_K
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_single__554e4a7f576b
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_xW_ne_yE
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_le__v_d8c333cc96ac
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_deg_le_total
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_comp_facts
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_fock_zero_right__d03fa504c8f6
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_term_val

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
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (z j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hβd : δv β + (j - a) • eWY = (LL.snoc LL.total).deg) (hβp : β (xW ρ) ≤ β (yE ρ))
    (hγd : δv γ + (j - a') • eWY = (LL.snoc LL.total).deg) (hγp : γ (xW ρ) ≤ γ (yE ρ))
    (h h' : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))))
    (hh' : ‖h'‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ)))) :
    IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kap N r B) * termF LL ρ z j a a' β γ h h' m) := by
  have hxy := xW_ne_yE (N := N) ρ
  set s : Fin (N + 1 + 1) × Fin r →₀ ℕ := Finsupp.single (xW ρ) 1 + Finsupp.single (yE ρ) 1 with hs
  by_cases h1 : β (xW ρ) < a
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial, Dop_pow_monomial_lt _ _ hxy a _ h
      (by simp [Finsupp.single_apply, hxy]; exact h1), fock_zero_left]
    simp
  by_cases h2 : γ (xW ρ) < a'
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial (yE ρ) m γ, Dop_pow_monomial_lt _ _ hxy a' _ h'
      (by simp [Finsupp.single_apply, hxy]; exact h2), fock_zero_right']
    simp
  push_neg at h1 h2
  have hle : ∀ (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (t : ℕ), t ≤ δ (xW ρ) → δ (xW ρ) ≤ δ (yE ρ) → t • s ≤ δ := by
    intro δ t ht1 ht2 v
    simp only [hs, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hv1 : xW ρ = v
    · subst hv1; simp [Ne.symm hxy]; exact ht1
    · by_cases hv2 : yE ρ = v
      · subst hv2; simp [hv1]; omega
      · simp [hv1, hv2]
  obtain ⟨β₀, rfl⟩ : ∃ β₀, β = β₀ + a • s := ⟨β - a • s, (tsub_add_cancel_of_le (hle β a h1 hβp)).symm⟩
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀, γ = γ₀ + a' • s := ⟨γ - a' • s, (tsub_add_cancel_of_le (hle γ a' h2 hγp)).symm⟩
  by_cases hb : β₀ = γ₀
  swap
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [fock_Dop_term _ _ hxy, if_neg hb]
    simp
  subst hb
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  have hoS : o ≤ S := deg_le_total LL (Fin.last N)

  have hsδ : ∀ t : ℕ, δv (t • s) = Pi.single (Fin.castSucc (Fin.last N)) t + Pi.single (Fin.last (N + 1)) t := by
    intro t
    rw [hs, smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one, δv_add,
      δv_single', δv_single']
  have hβd' : δv β₀ + Pi.single (Fin.castSucc (Fin.last N)) a + Pi.single (Fin.last (N + 1)) a + (j - a) • eWY =
      (LL.snoc LL.total).deg := by
    rw [← hβd, δv_add, hsδ, add_assoc (δv β₀)]
  obtain ⟨hk, hW, hY⟩ := comp_facts LL (j - a) β₀ a a hβd'
  set e := β₀ (yE ρ) + a with he
  set e' := β₀ (yE ρ) + a' with he'
  have heS : e ≤ S - (j - a) := by
    have := le_δv β₀ (Fin.last (N + 1)) ρ
    simp only [yE] at he
    omega
  set c1 := o + S + r + z - 1 - j with hc1
  set d1 := (β₀ (xW ρ) + a).descFactorial a with hd1
  set d2 := (β₀ (xW ρ) + a').descFactorial a' with hd2
  set δh := β₀ + Finsupp.single (yE ρ) a with hδh
  set Num := j.choose a * j.choose a' * d1 * d2 * a'.factorial * ∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial
    with hNum
  set Den := o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial with hDen
  set K : ℚ_[p] := (p : ℚ_[p]) ^ (kap N r B) * ((-1 : ℚ_[p]) ^ j * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p]))
    with hK
  have nd1 : d1 ≠ 0 := by
    rw [hd1]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have nd2 : d2 ≠ 0 := by
    rw [hd2]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have hNum0 : Num ≠ 0 := by
    rw [hNum]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero
      (Nat.choose_pos ha).ne' (Nat.choose_pos ha').ne') nd1) nd2) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos hj).ne'
      (pow_ne_zero _ (Nat.factorial_pos _).ne')) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')

  have hδv : δv δh = δv β₀ + Pi.single (Fin.last (N + 1)) a := by rw [hδh, δv_add, δv_single']
  have hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k :=
    fun k h => Fin.castSucc_ne_last k h.symm
  have hKn : ‖K‖ ≤ 1 := by
    rw [hK]
    refine norm_K _ h h' _ _ hh hh' Num Den hNum0 hDen0 _ (by simp) ?_
    rw [hNum, hDen]
    refine term_val LL hr B hB j a a' hj ha ha' δh ?_ ?_ ?_ d1 d2 ?_ nd1 ?_ nd2
    · intro k
      rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (hne _).symm, add_zero, hk k]
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (Fin.castSucc_ne_last _), add_zero]; omega
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_pos rfl]; omega
    · rw [hd1]; exact vdesc_ge _ _ (by omega)
    · rw [hd2]; exact vdesc_ge _ _ (by omega)
  have I1 := ((IVP.choose_add (p := p) c1 (o - j)).mul (IVP.choose_add e e)).mul (IVP.choose_add e' a')
  refine ((I1.smul K hKn).mono (by omega)).congr ?_
  intro m
  unfold termF
  rw [fock_Dop_term _ _ hxy, if_pos rfl, Nat.add_sub_cancel]
  have hjM : j ≤ o + (m + S) + r + z - 1 := by omega
  have hMj : o + (m + S) + r + z - 1 - j = m + c1 := by omega
  have hMo : (((o + (m + S) + r + z - 1).choose o : ℕ) : ℚ_[p]) =
      (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) *
        (((o + (m + S) + r + z - 1 - j).choose (o - j) : ℕ) : ℚ_[p]) / ((o.choose j : ℕ) : ℚ_[p]) := by
    have := Nat.choose_mul (n := o + (m + S) + r + z - 1) (k := o) (s := j) hj
    rw [eq_div_iff (by exact_mod_cast (Nat.choose_pos hj).ne')]
    exact_mod_cast this
  rw [hMo, hMj, Nat.descFactorial_eq_factorial_mul_choose (m + e') a']
  have hwf : wf (p := p) δh = ((∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial : ℕ) : ℚ_[p]) := by
    unfold wf; push_cast; rfl
  rw [hwf, hK, hNum, hDen]
  have n1 : (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjM).ne'
  have n2 : ((o.choose j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have n3 : ((j.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n4 : ((S.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n5 : ((m.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n6 : ((∏ i, (LL.deg i).factorial : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  push_cast at n6 ⊢
  rw [← hd1, ← hd2, ← he, ← ho, ← hS]
  have hc := mul_inv_cancel₀ n1
  have hm := mul_inv_cancel₀ n5
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-((p : ℚ_[p]) ^ kap N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹)) * hc +
    (-((p : ℚ_[p]) ^ kap N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹) *
      ((((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) * (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹)) * hm
end Formalism.GM.gammaIntegralityLemmas
