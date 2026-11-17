-- Prove2me | solution 1 for CritWinSpin.p4c_1_1_ii_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T07:17:27.393431+00:00
-- url     : https://prove2.me/submissions/44a9cb87-e801-43f6-9308-4e5cc8d66002

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_BilinearFamily
import Definitions.Def_CritWinSpin_errExt
import Definitions.Def_CritWinSpin_Lhat

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace CritWinSpin

private lemma p4c11_polyBounded_add {f g : ℕ → ℕ} (hf : PolyBounded f) (hg : PolyBounded g) :
    PolyBounded (fun d => f d + g d) := by
  obtain ⟨k₁, hk₁⟩ := hf
  obtain ⟨k₂, hk₂⟩ := hg
  refine ⟨max k₁ k₂ + 2 + (k₁ + k₂), fun d => ?_⟩
  have h1 := hk₁ d
  have h2 := hk₂ d
  by_cases hd0 : d = 0
  · subst hd0
    have hpow0 : (0 : ℕ) ^ (max k₁ k₂ + 2 + (k₁ + k₂)) = 0 := zero_pow (by omega)
    rw [hpow0, zero_add]
    have hk1_0 : f 0 ≤ 1 + k₁ := by
      rcases k₁ with _ | k₁
      · simp only [pow_zero, add_zero] at h1; exact h1
      · simp only [Nat.zero_pow (Nat.succ_pos _), zero_add] at h1; omega
    have hk2_0 : g 0 ≤ 1 + k₂ := by
      rcases k₂ with _ | k₂
      · simp only [pow_zero, add_zero] at h2; exact h2
      · simp only [Nat.zero_pow (Nat.succ_pos _), zero_add] at h2; omega
    have hadd0 : f 0 + g 0 ≤ (1 + k₁) + (1 + k₂) := add_le_add hk1_0 hk2_0
    have hmax0 : 0 ≤ max k₁ k₂ := Nat.zero_le _
    linarith [hadd0, hmax0]
  · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
    have hp1 : d ^ k₁ ≤ d ^ max k₁ k₂ := Nat.pow_le_pow_right hd1 (le_max_left _ _)
    have hp2 : d ^ k₂ ≤ d ^ max k₁ k₂ := Nat.pow_le_pow_right hd1 (le_max_right _ _)
    rcases (show 2 ≤ d ∨ d = 1 by omega) with hd2 | rfl
    · have h2pow : 2 * d ^ max k₁ k₂ ≤ d ^ (max k₁ k₂ + 1) := by
        calc 2 * d ^ max k₁ k₂ ≤ d * d ^ max k₁ k₂ := Nat.mul_le_mul_right _ hd2
          _ = d ^ (max k₁ k₂ + 1) := by rw [pow_succ']
      have hA : d ^ (max k₁ k₂ + 1) ≤ d ^ (max k₁ k₂ + 2 + (k₁ + k₂)) :=
        Nat.pow_le_pow_right hd1 (by omega)
      calc f d + g d ≤ (d ^ k₁ + k₁) + (d ^ k₂ + k₂) := add_le_add h1 h2
        _ ≤ 2 * d ^ max k₁ k₂ + (k₁ + k₂) := by omega
        _ ≤ d ^ (max k₁ k₂ + 2 + (k₁ + k₂)) + (max k₁ k₂ + 2 + (k₁ + k₂)) := by omega
    · simp only [one_pow] at h1 h2 ⊢
      omega

private lemma p4c11_polyBounded_mul_pow {f : ℕ → ℕ} (hf : PolyBounded f) (m : ℕ) :
    PolyBounded (fun d => f d ^ m) := by
  obtain ⟨k, hk⟩ := hf
  let C : ℕ := k + 1
  have hf_le : ∀ d : ℕ, f d ≤ C * (d + 1) ^ k := by
    intro d
    have h1 := hk d
    have hpow : d ^ k ≤ (d + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ d) k
    have h1pow : 1 ≤ (d + 1) ^ k := Nat.one_le_pow k (d + 1) (Nat.succ_pos d)
    have hkc : k ≤ k * (d + 1) ^ k := Nat.le_mul_of_pos_right k h1pow
    dsimp [C]
    nlinarith only [h1, hpow, hkc]
  let K : ℕ := k * m + C ^ m * 2 ^ (k * m) + 1
  refine ⟨K, fun d => ?_⟩
  have hm_le : f d ^ m ≤ C ^ m * (d + 1) ^ (k * m) := by
    calc f d ^ m ≤ (C * (d + 1) ^ k) ^ m := Nat.pow_le_pow_left (hf_le d) m
      _ = C ^ m * ((d + 1) ^ k) ^ m := Nat.mul_pow _ _ _
      _ = C ^ m * (d + 1) ^ (k * m) := by rw [← pow_mul]
  rcases le_or_gt d 1 with hd1 | hd2
  · have hd_le2 : d + 1 ≤ 2 := by omega
    have hpow2 : (d + 1) ^ (k * m) ≤ 2 ^ (k * m) := Nat.pow_le_pow_left hd_le2 _
    have hprod : f d ^ m ≤ C ^ m * 2 ^ (k * m) :=
      hm_le.trans (Nat.mul_le_mul_left _ hpow2)
    have hK : C ^ m * 2 ^ (k * m) ≤ K := by omega
    exact hprod.trans (hK.trans (Nat.le_add_left _ _))
  · have hd2_le : d + 1 ≤ 2 * d := by omega
    have hpow2d : (d + 1) ^ (k * m) ≤ (2 * d) ^ (k * m) := Nat.pow_le_pow_left hd2_le _
    have hconst : C ^ m * 2 ^ (k * m) ≤ d ^ (C ^ m * 2 ^ (k * m) + 1) := by
      have h2pow : C ^ m * 2 ^ (k * m) ≤ 2 ^ (C ^ m * 2 ^ (k * m) + 1) :=
        (Nat.lt_two_pow_self (n := C ^ m * 2 ^ (k * m) + 1)).le.trans' (Nat.le_succ _)
      exact h2pow.trans (Nat.pow_le_pow_left hd2 _)
    calc f d ^ m ≤ C ^ m * (2 * d) ^ (k * m) := hm_le.trans (Nat.mul_le_mul_left _ hpow2d)
      _ = (C ^ m * 2 ^ (k * m)) * d ^ (k * m) := by rw [Nat.mul_pow]; ring
      _ ≤ d ^ (C ^ m * 2 ^ (k * m) + 1) * d ^ (k * m) := Nat.mul_le_mul_right _ hconst
      _ = d ^ K := by rw [← pow_add]; congr 1; dsimp [K]; omega
      _ ≤ d ^ K + K := Nat.le_add_right _ _

private lemma p4c11_polyBounded_const (c : ℕ) : PolyBounded (fun _ => c) :=
  ⟨c, fun _ => Nat.le_add_left c _⟩

private lemma p4c11_polyBounded_const_mul_pow_add (a b c : ℕ) :
    PolyBounded (fun d => a * d ^ b + c) := by
  refine ⟨b + a + c + 1, fun d => ?_⟩
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [zero_pow (by omega : b + a + c + 1 ≠ 0), zero_add]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp only [pow_zero, mul_one]; omega
    · simp [zero_pow hb0]; omega
  · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
    have ha : a ≤ d ^ (a + 1) ∨ d = 1 := by
      rcases eq_or_ne d 1 with rfl | hd1'
      · exact Or.inr rfl
      · have hd2 : 2 ≤ d := by omega
        left
        exact (Nat.lt_two_pow_self (n := a)).le.trans (Nat.pow_le_pow_left hd2 a) |>.trans
          (Nat.pow_le_pow_right hd1 (by omega))
    rcases ha with ha | rfl
    · have hmul : a * d ^ b ≤ d ^ (b + a + c + 1) := by
        calc a * d ^ b ≤ d ^ (a + 1) * d ^ b := Nat.mul_le_mul_right _ ha
          _ = d ^ (b + a + 1) := by rw [← pow_add]; congr 1; ring
          _ ≤ d ^ (b + a + c + 1) := Nat.pow_le_pow_right hd1 (by omega)
      exact (Nat.add_le_add_right hmul c).trans (Nat.add_le_add_left (by omega) _)
    · simp only [one_pow, mul_one]
      omega

private lemma p4c11_gadget_params (p : ℕ) (hp : 2 ≤ p) (w ε : ℝ) (hw : 1 ≤ w)
    (hε : 0 < ε) (hεd : ε < dExp p) :
    ∃ Ac Cc : ℕ, GadgetParams p w ε Ac Cc := by
  let Ac : ℕ := Nat.ceil (2 * w + 5)
  have hAc_ge : 2 * w + 5 ≤ (Ac : ℝ) := Nat.le_ceil _
  have hpR_ge : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
  have hp_pos : 0 < (p : ℝ) := by linarith
  have hεp_pos : 0 < ε * (p : ℝ) := mul_pos hε hp_pos
  let Cc : ℕ := max (Ac + 2) (Nat.ceil (((Ac : ℝ) + 3) / (ε * (p : ℝ))))
  refine ⟨Ac, Cc, ?_, ?_, ?_⟩
  · have hratio : (1 : ℝ) ≤ (p : ℝ) / ((p : ℝ) - 1) := (one_le_div hp1_pos).mpr (by linarith)
    have hmul : (Ac : ℝ) * 1 ≤ (Ac : ℝ) * ((p : ℝ) / ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg Ac)
    rw [mul_div_assoc]
    linarith
  · have hCc1 : (Ac : ℝ) + 2 ≤ (Cc : ℝ) := by exact_mod_cast le_max_left (Ac + 2) _
    have h1 : (1 : ℝ) * (Cc : ℝ) ≤ ((p : ℝ) - 1) * (Cc : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg Cc)
    linarith
  · have hCc2_nat : Nat.ceil (((Ac : ℝ) + 3) / (ε * (p : ℝ))) ≤ Cc := le_max_right (Ac + 2) _
    have hCc2 : ((Ac : ℝ) + 3) / (ε * (p : ℝ)) ≤ (Cc : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hCc2_nat)
    have hmul : (Ac : ℝ) + 3 ≤ (Cc : ℝ) * (ε * (p : ℝ)) := (div_le_iff₀ hεp_pos).mp hCc2
    have hdExp : dExp p < 1 := by
      unfold dExp
      rw [div_lt_one hp_pos]
      linarith
    linarith [show ε * (1 + (p : ℝ) * (Cc : ℝ)) = ε + (Cc : ℝ) * (ε * (p : ℝ)) by ring]

private lemma p4c11_Nf_bounds (p : ℕ) (n₀ : ℕ → ℕ)
    (hn₀_poly : PolyBounded n₀) (hn₀_sq : ∀ d, d ^ 2 ≤ n₀ d) (Cc : ℕ) :
    (∀ d, d ≤ (n₀ d + 1) * cloudSize p Cc (n₀ d + 1)) ∧
    PolyBounded (fun d => (n₀ d + 1) * cloudSize p Cc (n₀ d + 1)) := by
  refine ⟨fun d => ?_, ?_⟩
  · rcases eq_or_ne d 0 with rfl | hd0
    · exact Nat.zero_le _
    · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
      have hsq : d ≤ n₀ d + 1 := by
        calc d = d * 1 := (Nat.mul_one d).symm
          _ ≤ d * d := Nat.mul_le_mul_left d hd1
          _ = d ^ 2 := (sq d).symm
          _ ≤ n₀ d := hn₀_sq d
          _ ≤ n₀ d + 1 := Nat.le_succ _
      have hcloud : 1 ≤ cloudSize p Cc (n₀ d + 1) := by
        unfold cloudSize
        exact Nat.one_le_pow _ _ (Nat.succ_pos _)
      exact hsq.trans (Nat.le_mul_of_pos_right _ hcloud)
  · have hadd : PolyBounded (fun d => n₀ d + 1) :=
      p4c11_polyBounded_add hn₀_poly (p4c11_polyBounded_const 1)
    have hpow : PolyBounded (fun d => (n₀ d + 1) ^ (1 + p * Cc)) :=
      p4c11_polyBounded_mul_pow hadd (1 + p * Cc)
    convert hpow using 2 with d
    unfold cloudSize
    rw [pow_add, pow_one]

private lemma p4c11_poly_bounds (k n : ℕ → ℕ) (hk : PolyBounded k) (hn : PolyBounded n)
    (Ccap : ℝ) (hCcap : 0 < Ccap) :
    ∃ E D₀ CT : ℕ, 1 ≤ E ∧ 1 ≤ D₀ ∧ 1 ≤ CT ∧
      (∀ d, 1 ≤ d ^ E + D₀ ∧ k d ≤ d ^ E + D₀) ∧
      (∀ d, 1 ≤ CT * d ^ (2 * E) + CT ∧
        ⌈Ccap * (((d ^ E + D₀ : ℕ) : ℝ) + 1 + (n d : ℝ) ^ 2)⌉₊ ≤ CT * d ^ (2 * E) + CT) := by
  obtain ⟨k₁, hk₁⟩ := hk
  obtain ⟨k₂, hk₂⟩ := hn
  let E : ℕ := max k₁ k₂ + 1
  let D₀ : ℕ := k₁ + k₂ + 1
  let C₀ : ℕ := Nat.ceil (6 * Ccap) + 1
  let CT : ℕ := C₀ * D₀ ^ 2 + 1
  refine ⟨E, D₀, CT, by omega, by omega, by omega, fun d => ⟨by omega, ?_⟩, fun d => ⟨by omega, ?_⟩⟩
  · have hkd := hk₁ d
    rcases eq_or_ne d 0 with rfl | hd0
    · rcases k₁ with _ | k₁ <;> simp at hkd ⊢ <;> omega
    · have hp : d ^ k₁ ≤ d ^ E := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hd0) (by omega)
      omega
  · have hnd : n d ≤ d ^ E + D₀ := by
      have h2 := hk₂ d
      rcases eq_or_ne d 0 with rfl | hd0
      · rcases k₂ with _ | k₂ <;> simp at h2 ⊢ <;> omega
      · have hp : d ^ k₂ ≤ d ^ E := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hd0) (by omega)
        omega
    let Dd : ℝ := ((d ^ E + D₀ : ℕ) : ℝ)
    have hDd1 : (1 : ℝ) ≤ Dd := by
      have h1 : 1 ≤ d ^ E + D₀ := by omega
      dsimp [Dd]; exact_mod_cast h1
    have hndR : (n d : ℝ) ≤ Dd := by
      dsimp [Dd]; exact_mod_cast hnd
    have hsq1 : Dd + 1 + (n d : ℝ) ^ 2 ≤ 3 * Dd ^ 2 := by
      have hn_sq : (n d : ℝ) ^ 2 ≤ Dd ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hndR 2
      nlinarith [hDd1]
    have hsq2 : Dd ^ 2 ≤ 2 * (d : ℝ) ^ (2 * E) + 2 * (D₀ : ℝ) ^ 2 := by
      have hDd_eq : Dd = (d : ℝ) ^ E + (D₀ : ℝ) := by push_cast [Dd]; rfl
      rw [hDd_eq]
      have : ((d : ℝ) ^ E - (D₀ : ℝ)) ^ 2 ≥ 0 := sq_nonneg _
      have hpow : ((d : ℝ) ^ E) ^ 2 = (d : ℝ) ^ (2 * E) := by rw [← pow_mul, Nat.mul_comm E 2]
      nlinarith [hpow]
    have hC₀ : 6 * Ccap ≤ (C₀ : ℝ) := by
      have : 6 * Ccap ≤ (Nat.ceil (6 * Ccap) : ℝ) := Nat.le_ceil _
      have : (C₀ : ℝ) = (Nat.ceil (6 * Ccap) : ℝ) + 1 := by push_cast [C₀]; rfl
      linarith
    have hD₀1 : (1 : ℝ) ≤ (D₀ : ℝ) ^ 2 := by
      have : 1 ≤ D₀ := by omega
      have hR : (1 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast this
      nlinarith
    have hbound : Ccap * (Dd + 1 + (n d : ℝ) ^ 2) ≤ ((CT * d ^ (2 * E) + CT : ℕ) : ℝ) := by
      calc Ccap * (Dd + 1 + (n d : ℝ) ^ 2)
          ≤ Ccap * (3 * (2 * (d : ℝ) ^ (2 * E) + 2 * (D₀ : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hsq1.trans (by linarith)) hCcap.le
        _ = (6 * Ccap) * ((d : ℝ) ^ (2 * E) + (D₀ : ℝ) ^ 2) := by ring
        _ ≤ (C₀ : ℝ) * ((d : ℝ) ^ (2 * E) + (D₀ : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hC₀ (by positivity)
        _ ≤ ((C₀ : ℝ) * (D₀ : ℝ) ^ 2) * (d : ℝ) ^ (2 * E) + (C₀ : ℝ) * (D₀ : ℝ) ^ 2 := by
            have hd_nn : (0 : ℝ) ≤ (d : ℝ) ^ (2 * E) := by positivity
            have hC0_nn : (0 : ℝ) ≤ (C₀ : ℝ) := Nat.cast_nonneg _
            nlinarith [mul_le_mul_of_nonneg_left hD₀1 hd_nn]
        _ ≤ ((CT * d ^ (2 * E) + CT : ℕ) : ℝ) := by
            push_cast [CT]
            have : (0 : ℝ) ≤ (d : ℝ) ^ (2 * E) := by positivity
            nlinarith
    exact Nat.ceil_le.mpr hbound

private lemma p4c11_tau_pos (S : SpinLaw) : 0 < tau S := by
  have hvQ : 0 < varQ S := by
    have h1 : (0 : ℚ) < 1 ^ 2 * S.ρ 1 := by simpa using S.pos 1 S.one_mem
    have hnonneg : ∀ x ∈ S.A, (0 : ℚ) ≤ x ^ 2 * S.ρ x := fun x hx =>
      mul_nonneg (sq_nonneg x) (S.pos x hx).le
    exact lt_of_lt_of_le h1 (by rw [varQ]; exact Finset.single_le_sum hnonneg S.one_mem)
  unfold tau tauQ
  exact_mod_cast div_pos zero_lt_one hvQ

private lemma p4c11_zero_inst_props (S : SpinLaw) (p N : ℕ) (ε Cρ : ℝ) (hCρ : 0 < Cρ) :
    let I : Inst N := (0, 0)
    I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
      ((tau S * (1 + (N : ℝ) ^ (-dExp p + ε))) •
          (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef ∧
      width (castM I.1) (castV I.2) ≤ Cρ := by
  refine ⟨by ext i j; simp, rfl, ?_, ?_, ?_⟩
  · have : castM (0 : Matrix (Fin N) (Fin N) ℚ) = 0 := by ext i j; simp [castM]
    rw [this]
    exact Matrix.PosSemidef.zero
  · have hcast : castM (0 : Matrix (Fin N) (Fin N) ℚ) = 0 := by ext i j; simp [castM]
    rw [hcast, sub_zero]
    have hnonneg : 0 ≤ tau S * (1 + (N : ℝ) ^ (-dExp p + ε)) :=
      mul_nonneg (p4c11_tau_pos S).le (by positivity)
    exact Matrix.PosSemidef.one.smul hnonneg
  · have hM0 : castM (0 : Matrix (Fin N) (Fin N) ℚ) = 0 := by ext i j; simp [castM]
    have hV0 : castV (0 : Fin N → ℚ) = 0 := by ext i; simp [castV]
    unfold width
    rw [hM0, hV0]
    rcases isEmpty_or_nonempty (Fin N) with hE | _
    · rw [Real.iSup_of_isEmpty]; exact hCρ.le
    · exact ciSup_le fun _ => by simp [hCρ.le]

private lemma p4c11_gibbs_nonneg_sum_one (S : SpinLaw) (N : ℕ) (M : Inst N) :
    (∀ x : Config S (Fin N), 0 ≤ gibbs S (castM M.1) (castV M.2) x) ∧
    (∑ x : Config S (Fin N), gibbs S (castM M.1) (castV M.2) x = 1) := by
  have hw0 : ∀ x : Config S (Fin N), 0 ≤ gibbsWeight S (castM M.1) (castV M.2) x := fun x => by
    unfold gibbsWeight prodRho
    exact mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg fun _ _ => by exact_mod_cast (S.pos _ (Subtype.prop _)).le)
  have hZpos : 0 < ∑ x : Config S (Fin N), gibbsWeight S (castM M.1) (castV M.2) x := by
    refine Finset.sum_pos' (fun x _ => hw0 x)
      ⟨fun _ => ⟨1, S.one_mem⟩, Finset.mem_univ _, ?_⟩
    unfold gibbsWeight prodRho
    exact mul_pos (Real.exp_pos _)
      (Finset.prod_pos fun _ _ => by exact_mod_cast S.pos _ S.one_mem)
  refine ⟨fun x => div_nonneg (hw0 x) hZpos.le, ?_⟩
  unfold gibbs
  rw [← Finset.sum_div, div_self hZpos.ne']

private lemma p4c11_prod_sum_one {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (g : ι → α → ℝ) (hg : ∀ i, ∑ x : α, g i x = 1) :
    ∑ X : ι → α, ∏ i : ι, g i (X i) = 1 := by
  rw [← Fintype.prod_sum (fun i x => g i x)]
  exact Finset.prod_eq_one fun i _ => hg i

private def p4c11_consEquiv (α : Type*) (k : ℕ) : α × (Fin k → α) ≃ (Fin (k + 1) → α) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun j => f j.succ)
  left_inv p := Prod.ext rfl (funext fun j => by simp)
  right_inv f := funext fun j => Fin.cases rfl (fun j' => rfl) j

private def p4c11_splitEquiv (α : Type*) (k D : ℕ) (hkD : k ≤ D) :
    (Fin D → α) ≃ (Fin k → α) × (Fin (D - k) → α) where
  toFun X := (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩, fun j => X ⟨k + j.1, by omega⟩)
  invFun p j := if h : j.1 < k then p.1 ⟨j.1, h⟩ else p.2 ⟨j.1 - k, by omega⟩
  left_inv X := funext fun j => by
    by_cases h : j.1 < k
    · simp [h]
    · simp [h]
      congr 1
      ext
      dsimp
      omega
  right_inv p := Prod.ext
    (funext fun j => by simp [j.2])
    (funext fun j => by
      have hnk : ¬ (k + j.1 < k) := by omega
      simp [hnk])

private lemma p4c11_gibbsProd_split (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D)
    (M : Inst N) (X : Fin D → Config S (Fin N)) :
    gibbsProd S (castM M.1) (castV M.2) X =
      gibbsProd S (castM M.1) (castV M.2) (p4c11_splitEquiv _ k D hkD X).1 *
      gibbsProd S (castM M.1) (castV M.2) (p4c11_splitEquiv _ k D hkD X).2 := by
  unfold gibbsProd
  let g : Config S (Fin N) → ℝ := gibbs S (castM M.1) (castV M.2)
  let e : Fin k ⊕ Fin (D - k) ≃ Fin D :=
    finSumFinEquiv.trans (Fin.castOrderIso (Nat.add_sub_cancel' hkD)).toEquiv
  rw [← Equiv.prod_comp e]
  rw [Fintype.prod_sum_type]
  rfl

private lemma p4c11_tvDist_le_one {α : Type*} [Fintype α] (P Q : α → ℝ)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1) (hQ0 : ∀ x, 0 ≤ Q x) (hQ1 : ∑ x, Q x = 1) :
    tvDist P Q ≤ 1 := by
  unfold tvDist
  calc (∑ x, |P x - Q x|) / 2
      ≤ (∑ x, (P x + Q x)) / 2 := by
        refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => ?_) zero_le_two
        exact (abs_sub (P x) (Q x)).trans (by simp [abs_of_nonneg (hP0 x), abs_of_nonneg (hQ0 x)])
    _ = 1 := by rw [Finset.sum_add_distrib, hP1, hQ1]; norm_num

private lemma p4c11_prefix_mixture_bound_ext (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D)
    (Pi₀ : InstLaw N) (hPi0 : ∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) (hPi1 : ∑ M ∈ Pi₀.supp, Pi₀.prob M = 1)
    (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ)
    (hKs0 : ∀ M X o, 0 ≤ K_small M X o) (hKs1 : ∀ M X, ∑ o, K_small M X o = 1)
    (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ)
    (hRr0 : ∀ M X o, 0 ≤ R_rem M X o) (hRr1 : ∀ M X, ∑ o, R_rem M X o = 1)
    (w : ℝ) (hw_lo : 1 / (2 * (D : ℝ)) ≤ w) (hw_hi : w ≤ 1)
    (hK_mix : ∀ M X o,
      K_big M X o = w * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) o + (1 - w) * R_rem M X o) :
    1 - errExtKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errExtKernel S Pi₀ K_big) := by
  classical
  have hw0 : 0 ≤ w := le_trans (by positivity) hw_lo
  have h1w0 : 0 ≤ 1 - w := sub_nonneg.mpr hw_hi
  let eX := p4c11_splitEquiv (Config S (Fin N)) k D hkD
  let Zs := {M : Inst N // M ∈ Pi₀.supp} × ((Fin k → Config S (Fin N)) × Option (Config S (Fin N)))
  let Zb := {M : Inst N // M ∈ Pi₀.supp} × ((Fin D → Config S (Fin N)) × Option (Config S (Fin N)))
  let P_s : Zs → ℝ := fun z => Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * K_small z.1.1 z.2.1 z.2.2
  let Q_s : Zs → ℝ := fun z => Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * gibbsOpt S (castM z.1.1.1) (castV z.1.1.2) z.2.2
  let P_sl : Zb → ℝ := fun z => Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * K_small z.1.1 (eX z.2.1).1 z.2.2
  let P_r : Zb → ℝ := fun z => Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * R_rem z.1.1 z.2.1 z.2.2
  let P_b : Zb → ℝ := fun z => Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * K_big z.1.1 z.2.1 z.2.2
  let Q_b : Zb → ℝ := fun z => Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * gibbsOpt S (castM z.1.1.1) (castV z.1.1.2) z.2.2
  have hgibbs0 : ∀ (M : Inst N) (x : Config S (Fin N)), 0 ≤ gibbs S (castM M.1) (castV M.2) x :=
    fun M x => (p4c11_gibbs_nonneg_sum_one S N M).1 x
  have hgibbs1 : ∀ (M : Inst N), ∑ x : Config S (Fin N), gibbs S (castM M.1) (castV M.2) x = 1 :=
    fun M => (p4c11_gibbs_nonneg_sum_one S N M).2
  have hgp0 : ∀ {m : ℕ} (M : Inst N) (X : Fin m → Config S (Fin N)), 0 ≤ gibbsProd S (castM M.1) (castV M.2) X :=
    fun M X => Finset.prod_nonneg fun _ _ => hgibbs0 M _
  have hgo0 : ∀ (M : Inst N) (o : Option (Config S (Fin N))), 0 ≤ gibbsOpt S (castM M.1) (castV M.2) o := by
    intro M o; cases o with
    | none => simp [gibbsOpt]
    | some x => exact hgibbs0 M x
  have hsum_K : ∀ {m : ℕ} (K : Inst N → (Fin m → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ)
      (_hK1 : ∀ M X, ∑ o, K M X o = 1),
      ∑ z : {M : Inst N // M ∈ Pi₀.supp} × ((Fin m → Config S (Fin N)) × Option (Config S (Fin N))),
        Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 * K z.1.1 z.2.1 z.2.2 = 1 := by
    intro m K hK1
    rw [Fintype.sum_prod_type]
    calc ∑ M : {M // M ∈ Pi₀.supp}, ∑ p : (Fin m → Config S (Fin N)) × Option (Config S (Fin N)),
          Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) p.1 * K M.1 p.1 p.2
        = ∑ M : {M // M ∈ Pi₀.supp}, Pi₀.prob M.1 * ∑ X : Fin m → Config S (Fin N),
            gibbsProd S (castM M.1.1) (castV M.1.2) X * ∑ o, K M.1 X o := by
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [Fintype.sum_prod_type]
          calc ∑ X : Fin m → Config S (Fin N), ∑ o : Option (Config S (Fin N)),
                Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X * K M.1 X o
              = ∑ X, ∑ o, Pi₀.prob M.1 * (gibbsProd S (castM M.1.1) (castV M.1.2) X * K M.1 X o) := by
                refine Finset.sum_congr rfl fun X _ => Finset.sum_congr rfl fun o _ => mul_assoc _ _ _
            _ = Pi₀.prob M.1 * ∑ X, ∑ o, gibbsProd S (castM M.1.1) (castV M.1.2) X * K M.1 X o := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun X _ => (Finset.mul_sum _ _ _).symm
            _ = Pi₀.prob M.1 * ∑ X, gibbsProd S (castM M.1.1) (castV M.1.2) X * ∑ o, K M.1 X o := by
                congr 1; exact Finset.sum_congr rfl fun X _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ M : {M // M ∈ Pi₀.supp}, Pi₀.prob M.1 := by
          refine Finset.sum_congr rfl fun M _ => ?_
          simp_rw [hK1, mul_one]
          unfold gibbsProd
          rw [p4c11_prod_sum_one _ (fun _ => hgibbs1 M.1), mul_one]
      _ = 1 := (Finset.sum_coe_sort Pi₀.supp fun M => Pi₀.prob M).trans hPi1
  have hsum_Q : ∀ (m : ℕ),
      ∑ z : {M : Inst N // M ∈ Pi₀.supp} × ((Fin m → Config S (Fin N)) × Option (Config S (Fin N))),
        Pi₀.prob z.1.1 * gibbsProd S (castM z.1.1.1) (castV z.1.1.2) z.2.1 *
          gibbsOpt S (castM z.1.1.1) (castV z.1.1.2) z.2.2 = 1 := fun m => by
    refine hsum_K (fun M _ o => gibbsOpt S (castM M.1) (castV M.2) o) fun M _ => ?_
    rw [Fintype.sum_option, gibbsOpt, zero_add]
    exact hgibbs1 M
  have hPs0 : ∀ z, 0 ≤ P_s z := fun z => mul_nonneg (mul_nonneg (hPi0 z.1.1 z.1.2) (hgp0 _ _)) (hKs0 _ _ _)
  have hPr0 : ∀ z, 0 ≤ P_r z := fun z => mul_nonneg (mul_nonneg (hPi0 z.1.1 z.1.2) (hgp0 _ _)) (hRr0 _ _ _)
  have hQs0 : ∀ z, 0 ≤ Q_s z := fun z => mul_nonneg (mul_nonneg (hPi0 z.1.1 z.1.2) (hgp0 _ _)) (hgo0 _ _)
  have hQb0 : ∀ z, 0 ≤ Q_b z := fun z => mul_nonneg (mul_nonneg (hPi0 z.1.1 z.1.2) (hgp0 _ _)) (hgo0 _ _)
  have hPs1 : ∑ z, P_s z = 1 := hsum_K K_small hKs1
  have hPr1 : ∑ z, P_r z = 1 := hsum_K R_rem hRr1
  have hQs1 : ∑ z, Q_s z = 1 := hsum_Q k
  have hQb1 : ∑ z, Q_b z = 1 := hsum_Q D
  have hPb_eq : ∀ z, P_b z = w * P_sl z + (1 - w) * P_r z := fun z => by
    dsimp [P_b, P_sl, P_r, eX, p4c11_splitEquiv]
    rw [hK_mix]
    ring
  have hlift_eq : tvDist P_sl Q_b = errExtKernel S Pi₀ K_small := by
    unfold errExtKernel tvDist
    congr 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [← Equiv.sum_comp eX.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun X₁ _ => ?_
    rw [Finset.sum_comm]
    have htail1 : ∑ X₂ : Fin (D - k) → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X₂ = 1 :=
      p4c11_prod_sum_one _ (fun _ => hgibbs1 M.1)
    calc ∑ o : Option (Config S (Fin N)), ∑ X₂ : Fin (D - k) → Config S (Fin N),
          |P_sl (M, (eX.symm (X₁, X₂), o)) - Q_b (M, (eX.symm (X₁, X₂), o))|
        = ∑ o, ∑ X₂, |Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ o -
            Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * gibbsOpt S (castM M.1.1) (castV M.1.2) o| *
            gibbsProd S (castM M.1.1) (castV M.1.2) X₂ := by
          refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun X₂ _ => ?_
          have hsp := p4c11_gibbsProd_split S N k D hkD M.1 (eX.symm (X₁, X₂))
          have hpair := eX.apply_symm_apply (X₁, X₂)
          have h1 : (eX (eX.symm (X₁, X₂))).1 = X₁ := congrArg Prod.fst hpair
          have h2 : (eX (eX.symm (X₁, X₂))).2 = X₂ := congrArg Prod.snd hpair
          rw [h1, h2] at hsp
          dsimp [P_sl, Q_b]
          rw [h1, hsp, show Pi₀.prob M.1 * (gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * gibbsProd S (castM M.1.1) (castV M.1.2) X₂) * K_small M.1 X₁ o -
              Pi₀.prob M.1 * (gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * gibbsProd S (castM M.1.1) (castV M.1.2) X₂) * gibbsOpt S (castM M.1.1) (castV M.1.2) o =
              (Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ o -
               Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * gibbsOpt S (castM M.1.1) (castV M.1.2) o) *
              gibbsProd S (castM M.1.1) (castV M.1.2) X₂ by ring,
            abs_mul, abs_of_nonneg (hgp0 M.1 X₂)]
      _ = ∑ o, |Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ o -
            Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * gibbsOpt S (castM M.1.1) (castV M.1.2) o| := by
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [← Finset.mul_sum, htail1, mul_one]
  have hconv : errExtKernel S Pi₀ K_big ≤ w * errExtKernel S Pi₀ K_small + (1 - w) * tvDist P_r Q_b := by
    rw [← hlift_eq]
    have hKb_eq : errExtKernel S Pi₀ K_big = tvDist P_b Q_b := rfl
    rw [hKb_eq]
    unfold tvDist
    calc (∑ z, |P_b z - Q_b z|) / 2
        ≤ (∑ z, (w * |P_sl z - Q_b z| + (1 - w) * |P_r z - Q_b z|)) / 2 := by
          refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ?_) zero_le_two
          rw [hPb_eq z, show w * P_sl z + (1 - w) * P_r z - Q_b z = w * (P_sl z - Q_b z) + (1 - w) * (P_r z - Q_b z) by ring]
          refine (abs_add_le _ _).trans_eq ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg h1w0]
      _ = w * ((∑ z, |P_sl z - Q_b z|) / 2) + (1 - w) * ((∑ z, |P_r z - Q_b z|) / 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  have htv_r_le1 : tvDist P_r Q_b ≤ 1 := p4c11_tvDist_le_one P_r Q_b hPr0 hPr1 hQb0 hQb1
  have htv_s_le1 : errExtKernel S Pi₀ K_small ≤ 1 := by
    have hKs_eq : errExtKernel S Pi₀ K_small = tvDist P_s Q_s := rfl
    rw [hKs_eq]
    exact p4c11_tvDist_le_one P_s Q_s hPs0 hPs1 hQs0 hQs1
  have hw_ineq : w * (1 - errExtKernel S Pi₀ K_small) ≤ 1 - errExtKernel S Pi₀ K_big := by
    have := mul_le_mul_of_nonneg_left htv_r_le1 h1w0
    linarith [hconv]
  have hdiff_nn : 0 ≤ 1 - errExtKernel S Pi₀ K_small := sub_nonneg.mpr htv_s_le1
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hD1
  have h1 : (1 / (2 * (D : ℝ))) * (1 - errExtKernel S Pi₀ K_small) ≤ w * (1 - errExtKernel S Pi₀ K_small) :=
    mul_le_mul_of_nonneg_right hw_lo hdiff_nn
  have h2 : (1 / (2 * (D : ℝ))) * (1 - errExtKernel S Pi₀ K_small) ≤ 1 - errExtKernel S Pi₀ K_big :=
    h1.trans hw_ineq
  have h2Dpos : (0 : ℝ) < 2 * (D : ℝ) := by positivity
  calc 1 - errExtKernel S Pi₀ K_small
      = 2 * (D : ℝ) * ((1 / (2 * (D : ℝ))) * (1 - errExtKernel S Pi₀ K_small)) := by
        field_simp [h2Dpos.ne']
    _ ≤ 2 * (D : ℝ) * (1 - errExtKernel S Pi₀ K_big) :=
        mul_le_mul_of_nonneg_left h2 h2Dpos.le

private lemma p4c11_prefix_mixture_bound_amp (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D)
    (Pi₀ : InstLaw N) (hPi0 : ∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) (hPi1 : ∑ M ∈ Pi₀.supp, Pi₀.prob M = 1)
    (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ)
    (hKs0 : ∀ M X o, 0 ≤ K_small M X o) (hKs1 : ∀ M X, ∑ o, K_small M X o = 1)
    (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Fin (D + 1) → Config S (Fin N)) → ℝ)
    (hRr0 : ∀ M X o, 0 ≤ R_rem M X o) (hRr1 : ∀ M X, ∑ o, R_rem M X o = 1)
    (w : ℝ) (hw_lo : 1 / (2 * (D : ℝ)) ≤ w) (hw_hi : w ≤ 1)
    (hK_mix : ∀ M (X : Fin D → Config S (Fin N)) o,
      K_big M X o = w * ∑ y : Option (Fin (k + 1) → Config S (Fin N)),
          (if Option.map (fun Y (j : Fin (D + 1)) =>
              if h : j.1 < k + 1 then Y ⟨j.1, h⟩ else X ⟨k + (j.1 - (k + 1)), by omega⟩) y = o
            then (1 : ℝ) else 0) * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) y +
        (1 - w) * R_rem M X o) :
    1 - errAmpKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errAmpKernel S Pi₀ K_big) := by
  classical
  have hw0 : 0 ≤ w := le_trans (by positivity) hw_lo
  have h1w0 : 0 ≤ 1 - w := sub_nonneg.mpr hw_hi
  let eX := p4c11_splitEquiv (Config S (Fin N)) k D hkD
  let eTail : (Fin (D - k) → Config S (Fin N)) ≃ (Fin (D + 1 - (k + 1)) → Config S (Fin N)) :=
    ⟨fun f j => f ⟨j.1, by omega⟩, fun g j => g ⟨j.1, by omega⟩, fun _ => rfl, fun _ => rfl⟩
  let eX' := eX.trans (Equiv.prodCongr (Equiv.refl _) eTail)
  let eZ := p4c11_splitEquiv (Config S (Fin N)) (k + 1) (D + 1) (Nat.succ_le_succ hkD)
  let K_pad : Inst N → (Fin D → Config S (Fin N)) → Option (Fin (D + 1) → Config S (Fin N)) → ℝ :=
    fun M X o => ∑ y : Option (Fin (k + 1) → Config S (Fin N)),
      (if Option.map (fun Y => eZ.symm (Y, (eX' X).2)) y = o then (1 : ℝ) else 0) * K_small M (eX' X).1 y
  let P_s : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin (k + 1) → Config S (Fin N)) → ℝ := fun z =>
    Pi₀.prob z.1.1 * ∑ X : Fin k → Config S (Fin N), gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K_small z.1.1 X z.2
  let Q_s : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin (k + 1) → Config S (Fin N)) → ℝ := fun z =>
    Pi₀.prob z.1.1 * gibbsTupleOpt S (castM z.1.1.1) (castV z.1.1.2) (k + 1) z.2
  let P_p : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin (D + 1) → Config S (Fin N)) → ℝ := fun z =>
    Pi₀.prob z.1.1 * ∑ X : Fin D → Config S (Fin N), gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K_pad z.1.1 X z.2
  let P_r : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin (D + 1) → Config S (Fin N)) → ℝ := fun z =>
    Pi₀.prob z.1.1 * ∑ X : Fin D → Config S (Fin N), gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * R_rem z.1.1 X z.2
  let P_b : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin (D + 1) → Config S (Fin N)) → ℝ := fun z =>
    Pi₀.prob z.1.1 * ∑ X : Fin D → Config S (Fin N), gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K_big z.1.1 X z.2
  let Q_b : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin (D + 1) → Config S (Fin N)) → ℝ := fun z =>
    Pi₀.prob z.1.1 * gibbsTupleOpt S (castM z.1.1.1) (castV z.1.1.2) (D + 1) z.2
  have hgibbs0 : ∀ (M : Inst N) (x : Config S (Fin N)), 0 ≤ gibbs S (castM M.1) (castV M.2) x :=
    fun M x => (p4c11_gibbs_nonneg_sum_one S N M).1 x
  have hgibbs1 : ∀ (M : Inst N), ∑ x : Config S (Fin N), gibbs S (castM M.1) (castV M.2) x = 1 :=
    fun M => (p4c11_gibbs_nonneg_sum_one S N M).2
  have hgp0 : ∀ {m : ℕ} (M : Inst N) (X : Fin m → Config S (Fin N)), 0 ≤ gibbsProd S (castM M.1) (castV M.2) X :=
    fun M X => Finset.prod_nonneg fun _ _ => hgibbs0 M _
  have hKp0 : ∀ M X o, 0 ≤ K_pad M X o := fun M X o => Finset.sum_nonneg fun y _ =>
    mul_nonneg (by split_ifs <;> norm_num) (hKs0 _ _ _)
  have hKp1 : ∀ M X, ∑ o, K_pad M X o = 1 := fun M X => by
    dsimp [K_pad]; rw [Finset.sum_comm]
    calc ∑ y : Option (Fin (k + 1) → Config S (Fin N)), ∑ o,
          (if Option.map (fun Y => eZ.symm (Y, (eX' X).2)) y = o then (1 : ℝ) else 0) * K_small M (eX' X).1 y
        = ∑ y, (∑ o, if Option.map (fun Y => eZ.symm (Y, (eX' X).2)) y = o then (1 : ℝ) else 0) * K_small M (eX' X).1 y :=
          Finset.sum_congr rfl fun y _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ y, K_small M (eX' X).1 y := Finset.sum_congr rfl fun y _ => by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), one_mul]
      _ = 1 := hKs1 _ _
  have hsum_P : ∀ {m₁ m₂ : ℕ} (K : Inst N → (Fin m₁ → Config S (Fin N)) → Option (Fin m₂ → Config S (Fin N)) → ℝ)
      (_hK1 : ∀ M X, ∑ o, K M X o = 1),
      ∑ z : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin m₂ → Config S (Fin N)),
        Pi₀.prob z.1.1 * ∑ X : Fin m₁ → Config S (Fin N), gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K z.1.1 X z.2 = 1 := by
    intro m₁ m₂ K hK1
    rw [Fintype.sum_prod_type]
    calc ∑ M : {M // M ∈ Pi₀.supp}, ∑ o, Pi₀.prob M.1 * ∑ X, gibbsProd S (castM M.1.1) (castV M.1.2) X * K M.1 X o
        = ∑ M : {M // M ∈ Pi₀.supp}, Pi₀.prob M.1 * ∑ X, gibbsProd S (castM M.1.1) (castV M.1.2) X * ∑ o, K M.1 X o := by
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [← Finset.mul_sum]; congr 1; rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun X _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ M : {M // M ∈ Pi₀.supp}, Pi₀.prob M.1 := by
          refine Finset.sum_congr rfl fun M _ => ?_
          simp_rw [hK1, mul_one]
          unfold gibbsProd
          rw [p4c11_prod_sum_one _ (fun _ => hgibbs1 M.1), mul_one]
      _ = 1 := (Finset.sum_coe_sort Pi₀.supp fun M => Pi₀.prob M).trans hPi1
  have hsum_Q : ∀ (m : ℕ),
      ∑ z : {M : Inst N // M ∈ Pi₀.supp} × Option (Fin m → Config S (Fin N)),
        Pi₀.prob z.1.1 * gibbsTupleOpt S (castM z.1.1.1) (castV z.1.1.2) m z.2 = 1 := fun m => by
    rw [Fintype.sum_prod_type]
    calc ∑ M : {M // M ∈ Pi₀.supp}, ∑ o, Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) m o
        = ∑ M : {M // M ∈ Pi₀.supp}, Pi₀.prob M.1 * ∑ o, gibbsTupleOpt S (castM M.1.1) (castV M.1.2) m o :=
          Finset.sum_congr rfl fun M _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ M : {M // M ∈ Pi₀.supp}, Pi₀.prob M.1 := by
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [Fintype.sum_option, gibbsTupleOpt, zero_add]
          unfold gibbsTupleOpt gibbsProd
          rw [p4c11_prod_sum_one _ (fun _ => hgibbs1 M.1), mul_one]
      _ = 1 := (Finset.sum_coe_sort Pi₀.supp fun M => Pi₀.prob M).trans hPi1
  have hPs0 : ∀ z, 0 ≤ P_s z := fun z => mul_nonneg (hPi0 z.1.1 z.1.2)
    (Finset.sum_nonneg fun X _ => mul_nonneg (hgp0 _ _) (hKs0 _ _ _))
  have hPr0 : ∀ z, 0 ≤ P_r z := fun z => mul_nonneg (hPi0 z.1.1 z.1.2)
    (Finset.sum_nonneg fun X _ => mul_nonneg (hgp0 _ _) (hRr0 _ _ _))
  have hQs0 : ∀ z, 0 ≤ Q_s z := fun z => mul_nonneg (hPi0 z.1.1 z.1.2) (by
    cases z.2 with
    | none => simp [gibbsTupleOpt]
    | some xs => exact hgp0 _ xs)
  have hQb0 : ∀ z, 0 ≤ Q_b z := fun z => mul_nonneg (hPi0 z.1.1 z.1.2) (by
    cases z.2 with
    | none => simp [gibbsTupleOpt]
    | some xs => exact hgp0 _ xs)
  have hPs1 : ∑ z, P_s z = 1 := hsum_P K_small hKs1
  have hPr1 : ∑ z, P_r z = 1 := hsum_P R_rem hRr1
  have hQs1 : ∑ z, Q_s z = 1 := hsum_Q (k + 1)
  have hQb1 : ∑ z, Q_b z = 1 := hsum_Q (D + 1)
  have hpad_eq : errAmpKernel S Pi₀ K_pad = errAmpKernel S Pi₀ K_small := by
    unfold errAmpKernel tvDist
    congr 1
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Fintype.sum_option, Fintype.sum_option]
    have hnone_P : (∑ X : Fin D → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X * K_pad M.1 X none) =
        ∑ X₁ : Fin k → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ none := by
      have hkp : ∀ X, K_pad M.1 X none = K_small M.1 (eX' X).1 none := fun X => by
        dsimp [K_pad]; rw [Fintype.sum_option]
        simp
      simp_rw [hkp]
      rw [← Equiv.sum_comp eX'.symm, Fintype.sum_prod_type]
      calc ∑ X₁ : Fin k → Config S (Fin N), ∑ X₂ : Fin (D + 1 - (k + 1)) → Config S (Fin N),
            gibbsProd S (castM M.1.1) (castV M.1.2) (eX'.symm (X₁, X₂)) * K_small M.1 (eX' (eX'.symm (X₁, X₂))).1 none
          = ∑ X₁, (gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ none) *
              ∑ X₂ : Fin (D + 1 - (k + 1)) → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X₂ := by
            refine Finset.sum_congr rfl fun X₁ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun X₂ _ => ?_
            have hsp := p4c11_gibbsProd_split S N k D hkD M.1 (eX'.symm (X₁, X₂))
            have hpair := eX'.apply_symm_apply (X₁, X₂)
            have h1 : (eX' (eX'.symm (X₁, X₂))).1 = X₁ := congrArg Prod.fst hpair
            have h2 : (eX' (eX'.symm (X₁, X₂))).2 = X₂ := congrArg Prod.snd hpair
            have h1e : (eX (eX'.symm (X₁, X₂))).1 = X₁ := h1
            have h2e : (eX (eX'.symm (X₁, X₂))).2 = eTail.symm X₂ :=
              congrArg Prod.snd (eX.apply_symm_apply (X₁, eTail.symm X₂))
            rw [h1e, h2e] at hsp
            have hgp_tail : gibbsProd S (castM M.1.1) (castV M.1.2) (eTail.symm X₂) =
                gibbsProd S (castM M.1.1) (castV M.1.2) X₂ := by
              unfold gibbsProd
              exact Equiv.prod_comp (Fin.castOrderIso (by omega : D - k = D + 1 - (k + 1))).toEquiv
                (fun j => gibbs S (castM M.1.1) (castV M.1.2) (X₂ j))
            rw [hsp, hgp_tail, h1]
            ring
        _ = _ := by
            have htail' : ∑ X₂ : Fin (D + 1 - (k + 1)) → Config S (Fin N),
                gibbsProd S (castM M.1.1) (castV M.1.2) X₂ = 1 := by
              unfold gibbsProd
              exact p4c11_prod_sum_one _ (fun _ => hgibbs1 M.1)
            rw [htail']
            simp
    have hnone_term : |Pi₀.prob M.1 * ∑ X, gibbsProd S (castM M.1.1) (castV M.1.2) X * K_pad M.1 X none -
          Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) (D + 1) none| =
        |Pi₀.prob M.1 * ∑ X₁, gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ none -
          Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) (k + 1) none| := by
      rw [hnone_P]; simp [gibbsTupleOpt]
    have hsome_term : (∑ Z' : Fin (D + 1) → Config S (Fin N),
          |Pi₀.prob M.1 * ∑ X, gibbsProd S (castM M.1.1) (castV M.1.2) X * K_pad M.1 X (some Z') -
            Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) (D + 1) (some Z')|) =
        ∑ Y' : Fin (k + 1) → Config S (Fin N),
          |Pi₀.prob M.1 * ∑ X₁, gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ (some Y') -
            Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) (k + 1) (some Y')| := by
      rw [← Equiv.sum_comp eZ.symm, Fintype.sum_prod_type]
      have htail1 : ∑ X₂ : Fin (D + 1 - (k + 1)) → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X₂ = 1 := by
        unfold gibbsProd
        exact p4c11_prod_sum_one _ (fun _ => hgibbs1 M.1)
      refine Finset.sum_congr rfl fun Y' _ => ?_
      have hsplit_inner : ∀ X₂' : Fin ((D + 1) - (k + 1)) → Config S (Fin N),
          (∑ X : Fin D → Config S (Fin N),
            gibbsProd S (castM M.1.1) (castV M.1.2) X * K_pad M.1 X (some (eZ.symm (Y', X₂')))) =
          gibbsProd S (castM M.1.1) (castV M.1.2) X₂' *
            ∑ X₁ : Fin k → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ (some Y') := by
        intro X₂'
        rw [← Equiv.sum_comp eX'.symm, Fintype.sum_prod_type, Finset.sum_comm]
        have hinner : ∀ X₂ : Fin (D + 1 - (k + 1)) → Config S (Fin N),
            (∑ X₁ : Fin k → Config S (Fin N),
              gibbsProd S (castM M.1.1) (castV M.1.2) (eX'.symm (X₁, X₂)) *
                K_pad M.1 (eX'.symm (X₁, X₂)) (some (eZ.symm (Y', X₂')))) =
            if X₂ = X₂' then
              gibbsProd S (castM M.1.1) (castV M.1.2) X₂' *
                ∑ X₁ : Fin k → Config S (Fin N), gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ (some Y')
            else 0 := by
          intro X₂
          calc ∑ X₁ : Fin k → Config S (Fin N),
                gibbsProd S (castM M.1.1) (castV M.1.2) (eX'.symm (X₁, X₂)) *
                  K_pad M.1 (eX'.symm (X₁, X₂)) (some (eZ.symm (Y', X₂')))
              = ∑ X₁, (gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * gibbsProd S (castM M.1.1) (castV M.1.2) X₂) *
                  (if X₂ = X₂' then K_small M.1 X₁ (some Y') else 0) := by
                refine Finset.sum_congr rfl fun X₁ _ => ?_
                have hsp := p4c11_gibbsProd_split S N k D hkD M.1 (eX'.symm (X₁, X₂))
                have hpX := eX'.apply_symm_apply (X₁, X₂)
                have h1X : (eX' (eX'.symm (X₁, X₂))).1 = X₁ := congrArg Prod.fst hpX
                have h2X : (eX' (eX'.symm (X₁, X₂))).2 = X₂ := congrArg Prod.snd hpX
                have h1e : (eX (eX'.symm (X₁, X₂))).1 = X₁ := h1X
                have h2e : (eX (eX'.symm (X₁, X₂))).2 = eTail.symm X₂ :=
                  congrArg Prod.snd (eX.apply_symm_apply (X₁, eTail.symm X₂))
                rw [h1e, h2e] at hsp
                have hgp_tail : gibbsProd S (castM M.1.1) (castV M.1.2) (eTail.symm X₂) =
                    gibbsProd S (castM M.1.1) (castV M.1.2) X₂ := by
                  unfold gibbsProd
                  exact Equiv.prod_comp (Fin.castOrderIso (by omega : D - k = D + 1 - (k + 1))).toEquiv
                    (fun j => gibbs S (castM M.1.1) (castV M.1.2) (X₂ j))
                rw [hgp_tail] at hsp
                have hkp : K_pad M.1 (eX'.symm (X₁, X₂)) (some (eZ.symm (Y', X₂'))) =
                    if X₂ = X₂' then K_small M.1 X₁ (some Y') else 0 := by
                  dsimp [K_pad]
                  rw [Fintype.sum_option, Option.map_none]
                  simp only [reduceCtorEq, ite_false]
                  rw [h1X, h2X, zero_mul, zero_add]
                  have heq_iff : ∀ Y : Fin (k + 1) → Config S (Fin N),
                      (Option.map (fun Y => eZ.symm (Y, X₂)) (some Y) = some (eZ.symm (Y', X₂'))) ↔ (Y = Y' ∧ X₂ = X₂') := by
                    intro Y
                    simp only [Option.map_some, Option.some.injEq, eZ.symm.apply_eq_iff_eq, Prod.mk.injEq]
                  by_cases hX2 : X₂ = X₂'
                  · subst hX2
                    simp only [ite_true]
                    have hY_iff : ∀ Y : Fin (k + 1) → Config S (Fin N),
                        (Option.map (fun Y => eZ.symm (Y, X₂)) (some Y) = some (eZ.symm (Y', X₂))) ↔ Y = Y' :=
                      fun Y => (heq_iff Y).trans ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
                    calc ∑ Y, (if Option.map (fun Y => eZ.symm (Y, X₂)) (some Y) = some (eZ.symm (Y', X₂)) then (1 : ℝ) else 0) * K_small M.1 X₁ (some Y)
                        = ∑ Y, (if Y = Y' then (1 : ℝ) else 0) * K_small M.1 X₁ (some Y) :=
                          Finset.sum_congr rfl fun Y _ => by rw [if_congr (hY_iff Y) rfl rfl]
                      _ = K_small M.1 X₁ (some Y') := by simp
                  · rw [if_neg hX2]
                    refine Finset.sum_eq_zero fun Y _ => ?_
                    have hne : ¬ (Option.map (fun Y => eZ.symm (Y, X₂)) (some Y) = some (eZ.symm (Y', X₂'))) := by
                      rw [heq_iff]; exact fun h => hX2 h.2
                    rw [if_neg hne, zero_mul]
                rw [hsp, hkp]
            _ = _ := by
                by_cases hX2 : X₂ = X₂'
                · subst hX2
                  simp only [ite_true, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun X₁ _ => by ring
                · simp [hX2]
        simp_rw [hinner, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      calc ∑ X₂' : Fin ((D + 1) - (k + 1)) → Config S (Fin N),
            |Pi₀.prob M.1 * ∑ X, gibbsProd S (castM M.1.1) (castV M.1.2) X * K_pad M.1 X (some (eZ.symm (Y', X₂'))) -
              Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) (D + 1) (some (eZ.symm (Y', X₂')))|
          = ∑ X₂' : Fin ((D + 1) - (k + 1)) → Config S (Fin N),
              |Pi₀.prob M.1 * ∑ X₁, gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ (some Y') -
                Pi₀.prob M.1 * gibbsTupleOpt S (castM M.1.1) (castV M.1.2) (k + 1) (some Y')| *
                gibbsProd S (castM M.1.1) (castV M.1.2) X₂' := by
            refine Finset.sum_congr rfl fun X₂' _ => ?_
            rw [hsplit_inner X₂']
            have hspZ := p4c11_gibbsProd_split S N (k + 1) (D + 1) (Nat.succ_le_succ hkD) M.1 (eZ.symm (Y', X₂'))
            have hpZ := eZ.apply_symm_apply (Y', X₂')
            have h1Z : (eZ (eZ.symm (Y', X₂'))).1 = Y' := congrArg Prod.fst hpZ
            have h2Z : (eZ (eZ.symm (Y', X₂'))).2 = X₂' := congrArg Prod.snd hpZ
            rw [h1Z, h2Z] at hspZ
            dsimp [gibbsTupleOpt]
            rw [hspZ, show Pi₀.prob M.1 * (gibbsProd S (castM M.1.1) (castV M.1.2) X₂' *
                  ∑ X₁, gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ (some Y')) -
                  Pi₀.prob M.1 * (gibbsProd S (castM M.1.1) (castV M.1.2) Y' * gibbsProd S (castM M.1.1) (castV M.1.2) X₂') =
                  (Pi₀.prob M.1 * ∑ X₁, gibbsProd S (castM M.1.1) (castV M.1.2) X₁ * K_small M.1 X₁ (some Y') -
                   Pi₀.prob M.1 * gibbsProd S (castM M.1.1) (castV M.1.2) Y') *
                  gibbsProd S (castM M.1.1) (castV M.1.2) X₂' by ring,
              abs_mul, abs_of_nonneg (hgp0 M.1 X₂')]
        _ = _ := by
            rw [← Finset.mul_sum, htail1, mul_one]
    rw [hnone_term, hsome_term]
  have hPb_eq : ∀ z, P_b z = w * P_p z + (1 - w) * P_r z := fun z => by
    dsimp [P_b, P_p, P_r, K_pad]
    have hsum_X : ∑ X : Fin D → Config S (Fin N),
        gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K_big z.1.1 X z.2 =
        w * ∑ X, gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K_pad z.1.1 X z.2 +
        (1 - w) * ∑ X, gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * R_rem z.1.1 X z.2 := by
      calc _ = ∑ X, (w * (gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * K_pad z.1.1 X z.2) +
            (1 - w) * (gibbsProd S (castM z.1.1.1) (castV z.1.1.2) X * R_rem z.1.1 X z.2)) := by
            refine Finset.sum_congr rfl fun X _ => ?_
            have hK := hK_mix z.1.1 X z.2
            have hKp_eq : K_pad z.1.1 X z.2 = ∑ y : Option (Fin (k + 1) → Config S (Fin N)),
                (if Option.map (fun Y (j : Fin (D + 1)) =>
                    if h : j.1 < k + 1 then Y ⟨j.1, h⟩ else X ⟨k + (j.1 - (k + 1)), by omega⟩) y = z.2
                  then (1 : ℝ) else 0) * K_small z.1.1 (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) y := rfl
            rw [hK, hKp_eq]
            ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum_X]
    ring
  have hconv : errAmpKernel S Pi₀ K_big ≤ w * errAmpKernel S Pi₀ K_small + (1 - w) * tvDist P_r Q_b := by
    rw [← hpad_eq]
    have hKb_eq : errAmpKernel S Pi₀ K_big = tvDist P_b Q_b := rfl
    have hKp_eq : errAmpKernel S Pi₀ K_pad = tvDist P_p Q_b := rfl
    rw [hKb_eq, hKp_eq]
    unfold tvDist
    calc (∑ z, |P_b z - Q_b z|) / 2
        ≤ (∑ z, (w * |P_p z - Q_b z| + (1 - w) * |P_r z - Q_b z|)) / 2 := by
          refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ?_) zero_le_two
          rw [hPb_eq z, show w * P_p z + (1 - w) * P_r z - Q_b z = w * (P_p z - Q_b z) + (1 - w) * (P_r z - Q_b z) by ring]
          refine (abs_add_le _ _).trans_eq ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg h1w0]
      _ = w * ((∑ z, |P_p z - Q_b z|) / 2) + (1 - w) * ((∑ z, |P_r z - Q_b z|) / 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  have htv_r_le1 : tvDist P_r Q_b ≤ 1 := p4c11_tvDist_le_one P_r Q_b hPr0 hPr1 hQb0 hQb1
  have htv_s_le1 : errAmpKernel S Pi₀ K_small ≤ 1 := by
    have hKs_eq : errAmpKernel S Pi₀ K_small = tvDist P_s Q_s := rfl
    rw [hKs_eq]
    exact p4c11_tvDist_le_one P_s Q_s hPs0 hPs1 hQs0 hQs1
  have hw_ineq : w * (1 - errAmpKernel S Pi₀ K_small) ≤ 1 - errAmpKernel S Pi₀ K_big := by
    have := mul_le_mul_of_nonneg_left htv_r_le1 h1w0
    linarith [hconv]
  have hdiff_nn : 0 ≤ 1 - errAmpKernel S Pi₀ K_small := sub_nonneg.mpr htv_s_le1
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast Nat.succ_le_iff.mp hD1
  have h1 : (1 / (2 * (D : ℝ))) * (1 - errAmpKernel S Pi₀ K_small) ≤ w * (1 - errAmpKernel S Pi₀ K_small) :=
    mul_le_mul_of_nonneg_right hw_lo hdiff_nn
  have h2 : (1 / (2 * (D : ℝ))) * (1 - errAmpKernel S Pi₀ K_small) ≤ 1 - errAmpKernel S Pi₀ K_big :=
    h1.trans hw_ineq
  have h2Dpos : (0 : ℝ) < 2 * (D : ℝ) := by positivity
  calc 1 - errAmpKernel S Pi₀ K_small
      = 2 * (D : ℝ) * ((1 / (2 * (D : ℝ))) * (1 - errAmpKernel S Pi₀ K_small)) := by
        field_simp [h2Dpos.ne']
    _ ≤ 2 * (D : ℝ) * (1 - errAmpKernel S Pi₀ K_big) :=
        mul_le_mul_of_nonneg_left h2 h2Dpos.le

private lemma p4c11_keyLiftLaw_valid (F : BilinearFamily) (d : ℕ) (hd : 1 ≤ d) {N : ℕ}
    (f : (desc : Str) → WatersKey F desc d → Inst N) :
    (∀ M ∈ (keyLiftLaw F d f).supp, 0 ≤ (keyLiftLaw F d f).prob M) ∧
    (∑ M ∈ (keyLiftLaw F d f).supp, (keyLiftLaw F d f).prob M = 1) := by
  let descOf : (Fin (Polynomial.eval (unary d).length F.gen.coins) → Bool) → Str :=
    fun ω => F.gen.alg (tupleCode [List.ofFn ω, unary d])
  have hdescGen : ∀ ω, GenSupport F.gen d (descOf ω) := fun ω => ⟨ω, rfl⟩
  have hcard_pos : ∀ ω, 0 < Fintype.card (WatersKey F (descOf ω) d) := by
    intro ω
    have hq := (F.prime d hd (descOf ω) (hdescGen ω)).pos
    letI : Nonempty (Fin (F.q (descOf ω))) := ⟨⟨0, hq⟩⟩
    letI : Nonempty (WatersKey F (descOf ω) d) := ⟨(⟨0, hq⟩, ⟨0, hq⟩, fun _ => ⟨0, hq⟩)⟩
    exact Fintype.card_pos
  refine ⟨fun M _ => ?_, ?_⟩
  · unfold keyLiftLaw keygenAvg
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun ω _ => by
      dsimp only
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun key _ => by split_ifs <;> norm_num))
  · have havg1 : keygenAvg F d (fun _ _ => (1 : ℝ)) = 1 := by
      unfold keygenAvg
      have hinner : ∀ ω, (1 / (Fintype.card (WatersKey F (descOf ω) d) : ℝ)) *
          ∑ _key : WatersKey F (descOf ω) d, (1 : ℝ) = 1 := by
        intro ω
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_div_mul_cancel]
        exact_mod_cast (hcard_pos ω).ne'
      have hsum_ω : (∑ ω : Fin (Polynomial.eval (unary d).length F.gen.coins) → Bool,
          (have desc := descOf ω;
           1 / (Fintype.card (WatersKey F desc d) : ℝ) * ∑ _key : WatersKey F desc d, (1 : ℝ))) =
          ∑ ω : Fin (Polynomial.eval (unary d).length F.gen.coins) → Bool, (1 : ℝ) :=
        Finset.sum_congr rfl fun ω _ => by dsimp only; exact hinner ω
      change 1 / (2 : ℝ) ^ Polynomial.eval (unary d).length F.gen.coins * _ = 1
      rw [hsum_ω, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, one_div_mul_cancel (by positivity)]
    rw [← havg1]
    have hmem : ∀ ω (key : WatersKey F (descOf ω) d),
        f (descOf ω) key ∈ (keyLiftLaw F d f).supp := by
      intro ω key
      dsimp [keyLiftLaw]
      rw [Finset.mem_biUnion]
      exact ⟨ω, Finset.mem_univ _, Finset.mem_image.mpr ⟨key, Finset.mem_univ _, rfl⟩⟩
    have hprob : ∀ M, (keyLiftLaw F d f).prob M =
        keygenAvg F d (fun desc key => if f desc key = M then (1 : ℝ) else 0) := fun _ => rfl
    simp_rw [hprob]
    unfold keygenAvg
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun ω _ => ?_
    dsimp only
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun key _ => ?_
    change ∑ x ∈ (keyLiftLaw F d f).supp, (if f (descOf ω) key = x then (1 : ℝ) else 0) = 1
    rw [Finset.sum_ite_eq, if_pos (hmem ω key)]

private lemma p4c11_pow_le_two_pow (K C : ℕ) : ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀, (C : ℝ) * (d : ℝ) ^ K ≤ (2 : ℝ) ^ d := by
  let d₀ : ℕ := max (2 * (K + 1)) (C * 2 ^ (K + 1) * (K + 1).factorial + 1)
  refine ⟨d₀, by omega, fun d hd => ?_⟩
  have hd_ge1 : 2 * (K + 1) ≤ d := le_trans (le_max_left _ _) hd
  have hd_ge2 : C * 2 ^ (K + 1) * (K + 1).factorial + 1 ≤ d := le_trans (le_max_right _ _) hd
  have hsum : (d.choose (K + 1) : ℝ) ≤ (2 : ℝ) ^ d := by
    have hmem : K + 1 ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    have h1 : d.choose (K + 1) ≤ ∑ i ∈ Finset.range (d + 1), d.choose i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
    rw [Nat.sum_range_choose] at h1
    exact_mod_cast h1
  have hdesc : ((K + 1).factorial : ℝ) * (d.choose (K + 1) : ℝ) = (Nat.descFactorial d (K + 1) : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose d (K + 1)).symm
  have hdesc_eq : (Nat.descFactorial d (K + 1) : ℝ) = ∏ i ∈ Finset.range (K + 1), ((d : ℝ) - (i : ℝ)) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi_le : i ≤ d := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hi_le]
  have hprod_ge : ((d : ℝ) / 2) ^ (K + 1) ≤ ∏ i ∈ Finset.range (K + 1), ((d : ℝ) - (i : ℝ)) := by
    have hconst : ((d : ℝ) / 2) ^ (K + 1) = ∏ _i ∈ Finset.range (K + 1), ((d : ℝ) / 2) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [hconst]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun i hi => ?_
    have hi_le : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : 2 * (i : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 * i ≤ d)
    linarith
  have hfac_pos : (0 : ℝ) < ((K + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (K + 1)
  have hchoose_ge : (d : ℝ) ^ (K + 1) / (2 ^ (K + 1) * ((K + 1).factorial : ℝ)) ≤ (d.choose (K + 1) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (d : ℝ) ^ (K + 1) = ((d : ℝ) / 2) ^ (K + 1) * 2 ^ (K + 1) := by
      rw [div_pow, div_mul_cancel₀ _ (by positivity)]
    rw [h1]
    have h2 : ((d : ℝ) / 2) ^ (K + 1) ≤ ((K + 1).factorial : ℝ) * (d.choose (K + 1) : ℝ) := by
      rw [hdesc, hdesc_eq]
      exact hprod_ge
    nlinarith [show (0 : ℝ) ≤ 2 ^ (K + 1) from by positivity]
  have hC_le : (C : ℝ) * (2 ^ (K + 1) * ((K + 1).factorial : ℝ)) ≤ (d : ℝ) := by
    have hC_nat : C * (2 ^ (K + 1) * (K + 1).factorial) ≤ d := by nlinarith [hd_ge2]
    exact_mod_cast hC_nat
  have hdK_nn : (0 : ℝ) ≤ (d : ℝ) ^ K := by positivity
  calc (C : ℝ) * (d : ℝ) ^ K
      = ((C : ℝ) * (2 ^ (K + 1) * ((K + 1).factorial : ℝ))) * (d : ℝ) ^ K /
          (2 ^ (K + 1) * ((K + 1).factorial : ℝ)) := by field_simp
    _ ≤ (d : ℝ) * (d : ℝ) ^ K / (2 ^ (K + 1) * ((K + 1).factorial : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC_le hdK_nn) (by positivity)
    _ = (d : ℝ) ^ (K + 1) / (2 ^ (K + 1) * ((K + 1).factorial : ℝ)) := by ring
    _ ≤ (d.choose (K + 1) : ℝ) := hchoose_ge
    _ ≤ (2 : ℝ) ^ d := hsum

private lemma p4c11_instLaw_shift_gen {N : ℕ} {α : Type*} [Fintype α]
    (Pi₀ Pi₁ : InstLaw N)
    (hPi0 : ∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) (hPi1 : ∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M)
    (hsub : Pi₁.supp ⊆ Pi₀.supp) (hzero : ∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0)
    (P_M Q_M : Inst N → α → ℝ)
    (hPM0 : ∀ M o, 0 ≤ P_M M o) (hPM1 : ∀ M, ∑ o, P_M M o = 1)
    (hQM0 : ∀ M o, 0 ≤ Q_M M o) (hQM1 : ∀ M, ∑ o, Q_M M o = 1) :
    tvDist (fun z : {M : Inst N // M ∈ Pi₀.supp} × α => Pi₀.prob z.1.1 * P_M z.1.1 z.2)
           (fun z : {M : Inst N // M ∈ Pi₀.supp} × α => Pi₀.prob z.1.1 * Q_M z.1.1 z.2) -
    tvDist (fun z : {M : Inst N // M ∈ Pi₁.supp} × α => Pi₁.prob z.1.1 * P_M z.1.1 z.2)
           (fun z : {M : Inst N // M ∈ Pi₁.supp} × α => Pi₁.prob z.1.1 * Q_M z.1.1 z.2) ≤
      ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M| := by
  let t : Inst N → ℝ := fun M => (∑ o : α, |P_M M o - Q_M M o|) / 2
  have ht0 : ∀ M, 0 ≤ t M := fun M => div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_two
  have ht1 : ∀ M, t M ≤ 1 := fun M =>
    p4c11_tvDist_le_one (P_M M) (Q_M M) (hPM0 M) (hPM1 M) (hQM0 M) (hQM1 M)
  have htv_eq : ∀ (Pi : InstLaw N) (_hPi : ∀ M ∈ Pi.supp, 0 ≤ Pi.prob M),
      tvDist (fun z : {M : Inst N // M ∈ Pi.supp} × α => Pi.prob z.1.1 * P_M z.1.1 z.2)
             (fun z : {M : Inst N // M ∈ Pi.supp} × α => Pi.prob z.1.1 * Q_M z.1.1 z.2) =
        ∑ M ∈ Pi.supp, Pi.prob M * t M := by
    intro Pi hPi
    unfold tvDist
    rw [Fintype.sum_prod_type]
    have hinner : ∀ M : {M : Inst N // M ∈ Pi.supp},
        (∑ o : α, |Pi.prob M.1 * P_M M.1 o - Pi.prob M.1 * Q_M M.1 o|) =
          Pi.prob M.1 * ∑ o : α, |P_M M.1 o - Q_M M.1 o| := by
      intro M
      calc ∑ o : α, |Pi.prob M.1 * P_M M.1 o - Pi.prob M.1 * Q_M M.1 o|
          = ∑ o : α, Pi.prob M.1 * |P_M M.1 o - Q_M M.1 o| := by
            refine Finset.sum_congr rfl fun o _ => ?_
            rw [← mul_sub, abs_mul, abs_of_nonneg (hPi M.1 M.2)]
        _ = Pi.prob M.1 * ∑ o : α, |P_M M.1 o - Q_M M.1 o| := (Finset.mul_sum _ _ _).symm
    calc (∑ M : {M // M ∈ Pi.supp}, ∑ o, |Pi.prob M.1 * P_M M.1 o - Pi.prob M.1 * Q_M M.1 o|) / 2
        = (∑ M : {M // M ∈ Pi.supp}, Pi.prob M.1 * ∑ o, |P_M M.1 o - Q_M M.1 o|) / 2 := by
          congr 1; exact Finset.sum_congr rfl fun M _ => hinner M
      _ = ∑ M : {M // M ∈ Pi.supp}, Pi.prob M.1 * t M := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun M _ => by dsimp [t]; ring
      _ = ∑ M ∈ Pi.supp, Pi.prob M * t M := Finset.sum_coe_sort Pi.supp fun M => Pi.prob M * t M
  have h1 : tvDist (fun z : {M : Inst N // M ∈ Pi₀.supp} × α => Pi₀.prob z.1.1 * P_M z.1.1 z.2)
                   (fun z : {M : Inst N // M ∈ Pi₀.supp} × α => Pi₀.prob z.1.1 * Q_M z.1.1 z.2) =
              ∑ M ∈ Pi₀.supp, Pi₀.prob M * t M := htv_eq Pi₀ hPi0
  have h2 : tvDist (fun z : {M : Inst N // M ∈ Pi₁.supp} × α => Pi₁.prob z.1.1 * P_M z.1.1 z.2)
                   (fun z : {M : Inst N // M ∈ Pi₁.supp} × α => Pi₁.prob z.1.1 * Q_M z.1.1 z.2) =
              ∑ M ∈ Pi₀.supp, Pi₁.prob M * t M := by
    rw [htv_eq Pi₁ hPi1]
    exact Finset.sum_subset hsub fun M hM0 hMn1 => by rw [hzero M hM0 hMn1, zero_mul]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun M _ => ?_
  calc Pi₀.prob M * t M - Pi₁.prob M * t M
      = (Pi₀.prob M - Pi₁.prob M) * t M := by ring
    _ ≤ |Pi₀.prob M - Pi₁.prob M| * t M := mul_le_mul_of_nonneg_right (le_abs_self _) (ht0 M)
    _ ≤ |Pi₀.prob M - Pi₁.prob M| * 1 := mul_le_mul_of_nonneg_left (ht1 M) (abs_nonneg _)
    _ = |Pi₁.prob M - Pi₀.prob M| := by rw [mul_one, abs_sub_comm]

private lemma p4c11_instLaw_shift_ext (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N)
    (hPi0 : ∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) (hPi1 : ∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M)
    (hsub : Pi₁.supp ⊆ Pi₀.supp) (hzero : ∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0)
    (K : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ)
    (hK0 : ∀ M X o, 0 ≤ K M X o) (hK1 : ∀ M X, ∑ o, K M X o = 1) :
    errExtKernel S Pi₀ K - errExtKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M| := by
  let P_M : Inst N → (Fin k → Config S (Fin N)) × Option (Config S (Fin N)) → ℝ := fun M p =>
    gibbsProd S (castM M.1) (castV M.2) p.1 * K M p.1 p.2
  let Q_M : Inst N → (Fin k → Config S (Fin N)) × Option (Config S (Fin N)) → ℝ := fun M p =>
    gibbsProd S (castM M.1) (castV M.2) p.1 * gibbsOpt S (castM M.1) (castV M.2) p.2
  have hPM0 : ∀ M p, 0 ≤ P_M M p := fun M p =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => (p4c11_gibbs_nonneg_sum_one S N M).1 _) (hK0 M p.1 p.2)
  have hPM1 : ∀ M, ∑ p, P_M M p = 1 := fun M => by
    dsimp [P_M]; rw [Fintype.sum_prod_type]
    calc ∑ X : Fin k → Config S (Fin N), ∑ o, gibbsProd S (castM M.1) (castV M.2) X * K M X o
        = ∑ X, gibbsProd S (castM M.1) (castV M.2) X * ∑ o, K M X o :=
          Finset.sum_congr rfl fun X _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ X : Fin k → Config S (Fin N), gibbsProd S (castM M.1) (castV M.2) X := by simp_rw [hK1, mul_one]
      _ = 1 := p4c11_prod_sum_one _ (fun _ => (p4c11_gibbs_nonneg_sum_one S N M).2)
  have hQM0 : ∀ M p, 0 ≤ Q_M M p := fun M p =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => (p4c11_gibbs_nonneg_sum_one S N M).1 _) (by
      cases p.2 with
      | none => simp [gibbsOpt]
      | some x => exact (p4c11_gibbs_nonneg_sum_one S N M).1 x)
  have hQM1 : ∀ M, ∑ p, Q_M M p = 1 := fun M => by
    dsimp [Q_M]; rw [Fintype.sum_prod_type]
    calc ∑ X : Fin k → Config S (Fin N), ∑ o, gibbsProd S (castM M.1) (castV M.2) X * gibbsOpt S (castM M.1) (castV M.2) o
        = ∑ X, gibbsProd S (castM M.1) (castV M.2) X * ∑ o, gibbsOpt S (castM M.1) (castV M.2) o :=
          Finset.sum_congr rfl fun X _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ X : Fin k → Config S (Fin N), gibbsProd S (castM M.1) (castV M.2) X := by
          refine Finset.sum_congr rfl fun X _ => ?_
          rw [Fintype.sum_option, gibbsOpt, zero_add]
          simp_rw [gibbsOpt]
          rw [(p4c11_gibbs_nonneg_sum_one S N M).2, mul_one]
      _ = 1 := by
          unfold gibbsProd
          exact p4c11_prod_sum_one _ (fun _ => (p4c11_gibbs_nonneg_sum_one S N M).2)
  unfold errExtKernel
  simp only [mul_assoc]
  exact p4c11_instLaw_shift_gen Pi₀ Pi₁ hPi0 hPi1 hsub hzero P_M Q_M hPM0 hPM1 hQM0 hQM1

private lemma p4c11_instLaw_shift_amp (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N)
    (hPi0 : ∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) (hPi1 : ∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M)
    (hsub : Pi₁.supp ⊆ Pi₀.supp) (hzero : ∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0)
    (K : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ)
    (hK0 : ∀ M X o, 0 ≤ K M X o) (hK1 : ∀ M X, ∑ o, K M X o = 1) :
    errAmpKernel S Pi₀ K - errAmpKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M| := by
  let P_M : Inst N → Option (Fin (k + 1) → Config S (Fin N)) → ℝ := fun M o =>
    ∑ X : Fin k → Config S (Fin N), gibbsProd S (castM M.1) (castV M.2) X * K M X o
  let Q_M : Inst N → Option (Fin (k + 1) → Config S (Fin N)) → ℝ := fun M o =>
    gibbsTupleOpt S (castM M.1) (castV M.2) (k + 1) o
  have hPM0 : ∀ M o, 0 ≤ P_M M o := fun M o => Finset.sum_nonneg fun X _ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => (p4c11_gibbs_nonneg_sum_one S N M).1 _) (hK0 M X o)
  have hPM1 : ∀ M, ∑ o, P_M M o = 1 := fun M => by
    dsimp [P_M]; rw [Finset.sum_comm]
    calc ∑ X : Fin k → Config S (Fin N), ∑ o, gibbsProd S (castM M.1) (castV M.2) X * K M X o
        = ∑ X, gibbsProd S (castM M.1) (castV M.2) X * ∑ o, K M X o :=
          Finset.sum_congr rfl fun X _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ X : Fin k → Config S (Fin N), gibbsProd S (castM M.1) (castV M.2) X := by simp_rw [hK1, mul_one]
      _ = 1 := p4c11_prod_sum_one _ (fun _ => (p4c11_gibbs_nonneg_sum_one S N M).2)
  have hQM0 : ∀ M o, 0 ≤ Q_M M o := fun M o => by
    cases o with
    | none => simp [Q_M, gibbsTupleOpt]
    | some xs =>
      dsimp [Q_M, gibbsTupleOpt, gibbsProd]
      exact Finset.prod_nonneg fun _ _ => (p4c11_gibbs_nonneg_sum_one S N M).1 _
  have hQM1 : ∀ M, ∑ o, Q_M M o = 1 := fun M => by
    dsimp [Q_M]; rw [Fintype.sum_option, gibbsTupleOpt, zero_add]
    exact p4c11_prod_sum_one _ (fun _ => (p4c11_gibbs_nonneg_sum_one S N M).2)
  unfold errAmpKernel
  exact p4c11_instLaw_shift_gen Pi₀ Pi₁ hPi0 hPi1 hsub hzero P_M Q_M hPM0 hPM1 hQM0 hQM1

private lemma p4c11_negligible_closure
    (Nf D T n₀ : ℕ → ℕ) (v₁ v₂ err_fn : ℕ → ℝ) (C Cv : ℝ) (hC : 0 < C) (hCv : 0 ≤ Cv)
    (F : BilinearFamily) (B : PPT) (hCDH : CDH F)
    (hNf_le : ∀ d, d ≤ Nf d) (hNf_poly : PolyBounded Nf)
    (hD_poly : PolyBounded D) (hT_poly : PolyBounded T)
    (hn₀_sq : ∀ d, d ^ 2 ≤ n₀ d)
    (hv₁ : ∀ d, v₁ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)))
    (hv₂ : ∀ d, v₂ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)))
    (herr : ∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 2 * (D d : ℝ) *
      (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d +
        ((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
        2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) :
    ∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 1 / (Nf d : ℝ) ^ c := by
  intro c
  obtain ⟨kN, hkN⟩ := hNf_poly
  obtain ⟨kD, hkD⟩ := hD_poly
  obtain ⟨kT, hkT⟩ := hT_poly
  obtain ⟨d_err, hd_err⟩ := herr
  let K_tot : ℕ := kD + 2 * kT + 1 + kN * c
  let M_Nf : ℕ := (kN + 1) ^ c
  let M_D : ℕ := kD + 1
  let M_T : ℕ := kT + 1
  let C_ceil : ℕ := Nat.ceil C + 1
  let Cv_ceil : ℕ := Nat.ceil Cv + 1
  let M₁ : ℕ := 2 * M_D * C_ceil * M_T * M_Nf
  let p_cdh : Polynomial ℕ := Polynomial.C (4 * M₁) * Polynomial.X ^ K_tot + Polynomial.C 1
  have hp_cdh_pos : ∀ n : ℕ, 1 ≤ p_cdh.eval n := by
    intro n
    simp only [p_cdh, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    omega
  obtain ⟨d_cdh, hd_cdh⟩ := hCDH B p_cdh hp_cdh_pos
  let M₂ : ℕ := 2 * M_D * (M_T + M_T ^ 2 + 1 + (2 + 2 * Cv_ceil) * M_T) * M_Nf
  obtain ⟨d_pow, hd_pow1, hd_pow⟩ := p4c11_pow_le_two_pow K_tot (4 * M₂)
  refine ⟨max 1 (max d_err (max d_cdh d_pow)), fun d hd => ?_⟩
  have hd1 : 1 ≤ d := le_trans (le_max_left _ _) hd
  have hd_e : d_err ≤ d := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hd)
  have hd_c : d_cdh ≤ d := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hd))
  have hd_p : d_pow ≤ d := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hd))
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hNf_pos : (0 : ℝ) < (Nf d : ℝ) := by
    have : 1 ≤ Nf d := hd1.trans (hNf_le d)
    exact_mod_cast this
  have hNf_pow_pos : (0 : ℝ) < (Nf d : ℝ) ^ c := pow_pos hNf_pos c
  have hpow1_le : ∀ e : ℕ, (1 : ℝ) ≤ (d : ℝ) ^ e := fun e => one_le_pow₀ hdR1
  have hD_le : (D d : ℝ) ≤ (M_D : ℝ) * (d : ℝ) ^ kD := by
    have h1 : D d ≤ d ^ kD + kD := hkD d
    have h2 : (D d : ℝ) ≤ (d : ℝ) ^ kD + (kD : ℝ) := by exact_mod_cast h1
    have h3 : (kD : ℝ) ≤ (kD : ℝ) * (d : ℝ) ^ kD := le_mul_of_one_le_right (Nat.cast_nonneg _) (hpow1_le kD)
    push_cast [M_D]; linarith
  have hT_le : (T d : ℝ) ≤ (M_T : ℝ) * (d : ℝ) ^ kT := by
    have h1 : T d ≤ d ^ kT + kT := hkT d
    have h2 : (T d : ℝ) ≤ (d : ℝ) ^ kT + (kT : ℝ) := by exact_mod_cast h1
    have h3 : (kT : ℝ) ≤ (kT : ℝ) * (d : ℝ) ^ kT := le_mul_of_one_le_right (Nat.cast_nonneg _) (hpow1_le kT)
    push_cast [M_T]; linarith
  have hNf_le_pow : (Nf d : ℝ) ^ c ≤ (M_Nf : ℝ) * (d : ℝ) ^ (kN * c) := by
    have h1 : (Nf d : ℝ) ≤ (kN + 1 : ℝ) * (d : ℝ) ^ kN := by
      have h' : (Nf d : ℝ) ≤ (d : ℝ) ^ kN + (kN : ℝ) := by exact_mod_cast hkN d
      have h'' : (kN : ℝ) ≤ (kN : ℝ) * (d : ℝ) ^ kN := le_mul_of_one_le_right (Nat.cast_nonneg _) (hpow1_le kN)
      linarith
    calc (Nf d : ℝ) ^ c ≤ ((kN + 1 : ℝ) * (d : ℝ) ^ kN) ^ c := pow_le_pow_left₀ hNf_pos.le h1 c
      _ = (kN + 1 : ℝ) ^ c * ((d : ℝ) ^ kN) ^ c := mul_pow _ _ _
      _ = (M_Nf : ℝ) * (d : ℝ) ^ (kN * c) := by push_cast [M_Nf]; rw [← pow_mul]
  have hsqrt_le : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hchoose_le : ((T d).choose 2 : ℝ) ≤ (T d : ℝ) ^ 2 := by
    have : (T d).choose 2 ≤ (T d) ^ 2 := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ 2).trans (by nlinarith [Nat.sub_le (T d) 1])
    exact_mod_cast this
  have hT_le_sq : (T d : ℝ) ≤ (M_T : ℝ) ^ 2 * (d : ℝ) ^ (2 * kT) := by
    have hM : (1 : ℝ) ≤ (M_T : ℝ) := by push_cast [M_T]; linarith
    have hd_mono : (d : ℝ) ^ kT ≤ (d : ℝ) ^ (2 * kT) := pow_le_pow_right₀ hdR1 (by omega)
    have hm : (M_T : ℝ) ≤ (M_T : ℝ) ^ 2 := by nlinarith
    exact hT_le.trans (mul_le_mul hm hd_mono (by positivity) (by positivity))
  have hTsq_le : (T d : ℝ) ^ 2 ≤ (M_T : ℝ) ^ 2 * (d : ℝ) ^ (2 * kT) := by
    calc (T d : ℝ) ^ 2 ≤ ((M_T : ℝ) * (d : ℝ) ^ kT) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hT_le 2
      _ = (M_T : ℝ) ^ 2 * (d : ℝ) ^ (2 * kT) := by rw [mul_pow, ← pow_mul, Nat.mul_comm kT 2]
  have hexp_n0 : Real.exp (-((n₀ d : ℝ) ^ 2)) ≤ 1 / (2 : ℝ) ^ d := by
    have hn_ge : (d : ℝ) ≤ (n₀ d : ℝ) ^ 2 := by
      have h1 : d ≤ n₀ d := by
        calc d = d * 1 := (Nat.mul_one d).symm
          _ ≤ d * d := Nat.mul_le_mul_left d hd1
          _ = d ^ 2 := (sq d).symm
          _ ≤ n₀ d := hn₀_sq d
      have h2 : n₀ d ≤ (n₀ d) ^ 2 := by
        have : 1 ≤ n₀ d := hd1.trans h1
        exact Nat.le_self_pow (by decide) (n₀ d)
      exact_mod_cast h1.trans h2
    have h3 : Real.exp (-((n₀ d : ℝ) ^ 2)) ≤ Real.exp (-(d : ℝ)) :=
      Real.exp_le_exp.mpr (neg_le_neg hn_ge)
    have h4 : (2 : ℝ) ^ d ≤ Real.exp (d : ℝ) := by
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc (2 : ℝ) ^ d ≤ (Real.exp 1) ^ d := pow_le_pow_left₀ (by norm_num) he1 d
        _ = Real.exp ((d : ℝ) * 1) := (Real.exp_nat_mul 1 d).symm
        _ = Real.exp (d : ℝ) := by rw [mul_one]
    have h5 : Real.exp (-(d : ℝ)) = 1 / Real.exp (d : ℝ) := by rw [Real.exp_neg, one_div]
    exact h3.trans (h5 ▸ one_div_le_one_div_of_le (by positivity) h4)
  have hC_le : C ≤ (C_ceil : ℝ) := (Nat.le_ceil C).trans (by push_cast [C_ceil]; linarith)
  have hCv_le : Cv ≤ (Cv_ceil : ℝ) := (Nat.le_ceil Cv).trans (by push_cast [Cv_ceil]; linarith)
  -- Bound Term 1 (CDH) * Nf(d)^c <= 1/4
  have hterm1 : (2 * (D d : ℝ) * (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d)) * (Nf d : ℝ) ^ c ≤ 1 / 4 := by
    have hpref_nn : 0 ≤ 2 * (D d : ℝ) * C * (T d : ℝ) * Real.sqrt (d : ℝ) * (Nf d : ℝ) ^ c := by positivity
    have hpref_le : 2 * (D d : ℝ) * C * (T d : ℝ) * Real.sqrt (d : ℝ) * (Nf d : ℝ) ^ c ≤
        (M₁ : ℝ) * (d : ℝ) ^ K_tot := by
      have hd_pow_eq : (d : ℝ) ^ kD * (d : ℝ) ^ kT * (d : ℝ) * (d : ℝ) ^ (kN * c) ≤ (d : ℝ) ^ K_tot := by
        have : (d : ℝ) ^ kD * (d : ℝ) ^ kT * (d : ℝ) ^ 1 * (d : ℝ) ^ (kN * c) =
            (d : ℝ) ^ (kD + kT + 1 + kN * c) := by simp only [← pow_add]
        rw [show (d : ℝ) ^ kD * (d : ℝ) ^ kT * (d : ℝ) * (d : ℝ) ^ (kN * c) =
            (d : ℝ) ^ kD * (d : ℝ) ^ kT * (d : ℝ) ^ 1 * (d : ℝ) ^ (kN * c) by ring, this]
        exact pow_le_pow_right₀ hdR1 (by omega)
      calc 2 * (D d : ℝ) * C * (T d : ℝ) * Real.sqrt (d : ℝ) * (Nf d : ℝ) ^ c
          ≤ 2 * ((M_D : ℝ) * (d : ℝ) ^ kD) * (C_ceil : ℝ) * ((M_T : ℝ) * (d : ℝ) ^ kT) *
              (d : ℝ) * ((M_Nf : ℝ) * (d : ℝ) ^ (kN * c)) := by
            gcongr
        _ = (M₁ : ℝ) * ((d : ℝ) ^ kD * (d : ℝ) ^ kT * (d : ℝ) * (d : ℝ) ^ (kN * c)) := by
            push_cast [M₁]; ring
        _ ≤ (M₁ : ℝ) * (d : ℝ) ^ K_tot := mul_le_mul_of_nonneg_left hd_pow_eq (Nat.cast_nonneg _)
    have hcdh_le : cdhAdv F B d ≤ 1 / ((4 * (M₁ : ℝ) * (d : ℝ) ^ K_tot) + 1) := by
      have h1 := hd_cdh d hd_c
      have hev : ((p_cdh.eval d : ℕ) : ℝ) = 4 * (M₁ : ℝ) * (d : ℝ) ^ K_tot + 1 := by
        simp [p_cdh]
      rwa [hev] at h1
    have hM_Nf_pos : 0 < M_Nf := pow_pos (Nat.succ_pos _) _
    have hM_D_pos : 0 < M_D := Nat.succ_pos _
    have hM_T_pos : 0 < M_T := Nat.succ_pos _
    have hC_ceil_pos : 0 < C_ceil := Nat.succ_pos _
    have hM1_nat_pos : 0 < M₁ := by
      dsimp [M₁]
      exact mul_pos (mul_pos (mul_pos (mul_pos (by decide) hM_D_pos) hC_ceil_pos) hM_T_pos) hM_Nf_pos
    have hM1_pos : 0 < (M₁ : ℝ) * (d : ℝ) ^ K_tot :=
      mul_pos (by exact_mod_cast hM1_nat_pos) (pow_pos (by linarith) _)
    have hcdh_le2 : cdhAdv F B d ≤ 1 / (4 * ((M₁ : ℝ) * (d : ℝ) ^ K_tot)) := by
      have hpos : 0 < 4 * ((M₁ : ℝ) * (d : ℝ) ^ K_tot) := mul_pos (by norm_num) hM1_pos
      exact hcdh_le.trans (one_div_le_one_div_of_le hpos (by linarith))
    have hM1R_ne : (M₁ : ℝ) ≠ 0 := by exact_mod_cast hM1_nat_pos.ne'
    have hdK_ne : (d : ℝ) ^ K_tot ≠ 0 := (pow_pos (by linarith : (0 : ℝ) < d) _).ne'
    calc (2 * (D d : ℝ) * (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d)) * (Nf d : ℝ) ^ c
        = (2 * (D d : ℝ) * C * (T d : ℝ) * Real.sqrt (d : ℝ) * (Nf d : ℝ) ^ c) * cdhAdv F B d := by ring
      _ ≤ (2 * (D d : ℝ) * C * (T d : ℝ) * Real.sqrt (d : ℝ) * (Nf d : ℝ) ^ c) *
            (1 / (4 * ((M₁ : ℝ) * (d : ℝ) ^ K_tot))) :=
          mul_le_mul_of_nonneg_left hcdh_le2 hpref_nn
      _ ≤ ((M₁ : ℝ) * (d : ℝ) ^ K_tot) * (1 / (4 * ((M₁ : ℝ) * (d : ℝ) ^ K_tot))) :=
          mul_le_mul_of_nonneg_right hpref_le (by positivity)
      _ = 1 / 4 := by field_simp [hM1R_ne, hdK_ne]
  -- Bound Term 2 (all 1 / 2^d and exp(-(n₀)^2) terms) * Nf(d)^c <= 1/4
  have hterm2 : (2 * (D d : ℝ) * (((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
      2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) * (Nf d : ℝ) ^ c ≤ 1 / 4 := by
    have hv12 : v₁ d + v₂ d ≤ 2 * (Cv_ceil : ℝ) * (T d : ℝ) * (1 / (2 : ℝ) ^ d) := by
      have h1 : v₁ d ≤ Cv * (T d : ℝ) * (1 / (2 : ℝ) ^ d) :=
        (hv₁ d).trans (mul_le_mul_of_nonneg_left hexp_n0 (by positivity))
      have h2 : v₂ d ≤ Cv * (T d : ℝ) * (1 / (2 : ℝ) ^ d) :=
        (hv₂ d).trans (mul_le_mul_of_nonneg_left hexp_n0 (by positivity))
      have h3 : Cv * (T d : ℝ) * (1 / (2 : ℝ) ^ d) ≤ (Cv_ceil : ℝ) * (T d : ℝ) * (1 / (2 : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCv_le (Nat.cast_nonneg _)) (by positivity)
      linarith
    have hexp_T : 2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) ≤ 2 * (T d : ℝ) * (1 / (2 : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left hexp_n0 (by positivity)
    have hinner : ((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
        2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d ≤
        (((T d : ℝ) + (T d : ℝ) ^ 2 + 1) + (2 + 2 * (Cv_ceil : ℝ)) * (T d : ℝ)) * (1 / (2 : ℝ) ^ d) := by
      have hch : ((T d).choose 2 : ℝ) * (1 / (2 : ℝ) ^ d) ≤ (T d : ℝ) ^ 2 * (1 / (2 : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_right hchoose_le (by positivity)
      linarith [hch, hexp_T, hv12]
    have hcoef_le : 2 * (D d : ℝ) * (((T d : ℝ) + (T d : ℝ) ^ 2 + 1) + (2 + 2 * (Cv_ceil : ℝ)) * (T d : ℝ)) *
        (Nf d : ℝ) ^ c ≤ (M₂ : ℝ) * (d : ℝ) ^ K_tot := by
      have hsumT : (T d : ℝ) + (T d : ℝ) ^ 2 + 1 + (2 + 2 * (Cv_ceil : ℝ)) * (T d : ℝ) ≤
          ((M_T : ℝ) + (M_T : ℝ) ^ 2 + 1 + (2 + 2 * (Cv_ceil : ℝ)) * (M_T : ℝ)) * (d : ℝ) ^ (2 * kT) := by
        have hd_mono : (d : ℝ) ^ kT ≤ (d : ℝ) ^ (2 * kT) := pow_le_pow_right₀ hdR1 (by omega)
        have hT1' : (T d : ℝ) ≤ (M_T : ℝ) * (d : ℝ) ^ (2 * kT) :=
          hT_le.trans (mul_le_mul_of_nonneg_left hd_mono (Nat.cast_nonneg _))
        have h1pow : (1 : ℝ) ≤ (d : ℝ) ^ (2 * kT) := hpow1_le (2 * kT)
        have hCv_nn : (0 : ℝ) ≤ 2 + 2 * (Cv_ceil : ℝ) := by positivity
        nlinarith [hT1', hTsq_le, h1pow]
      have hd_pow_eq : (d : ℝ) ^ kD * (d : ℝ) ^ (2 * kT) * (d : ℝ) ^ (kN * c) ≤ (d : ℝ) ^ K_tot := by
        rw [← pow_add, ← pow_add]
        exact pow_le_pow_right₀ hdR1 (by omega)
      calc 2 * (D d : ℝ) * (((T d : ℝ) + (T d : ℝ) ^ 2 + 1) + (2 + 2 * (Cv_ceil : ℝ)) * (T d : ℝ)) * (Nf d : ℝ) ^ c
          ≤ 2 * ((M_D : ℝ) * (d : ℝ) ^ kD) *
              (((M_T : ℝ) + (M_T : ℝ) ^ 2 + 1 + (2 + 2 * (Cv_ceil : ℝ)) * (M_T : ℝ)) * (d : ℝ) ^ (2 * kT)) *
              ((M_Nf : ℝ) * (d : ℝ) ^ (kN * c)) := by
            gcongr
        _ = (M₂ : ℝ) * ((d : ℝ) ^ kD * (d : ℝ) ^ (2 * kT) * (d : ℝ) ^ (kN * c)) := by
            push_cast [M₂]; ring
        _ ≤ (M₂ : ℝ) * (d : ℝ) ^ K_tot := mul_le_mul_of_nonneg_left hd_pow_eq (Nat.cast_nonneg _)
    have h2pow : 4 * (M₂ : ℝ) * (d : ℝ) ^ K_tot ≤ (2 : ℝ) ^ d := by
      have h1 := hd_pow d hd_p
      push_cast at h1 ⊢
      exact h1
    calc (2 * (D d : ℝ) * (((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
          2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) * (Nf d : ℝ) ^ c
        ≤ (2 * (D d : ℝ) * (((T d : ℝ) + (T d : ℝ) ^ 2 + 1) + (2 + 2 * (Cv_ceil : ℝ)) * (T d : ℝ)) *
            (Nf d : ℝ) ^ c) * (1 / (2 : ℝ) ^ d) := by
          have h1 := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * (D d : ℝ))
          have h2 := mul_le_mul_of_nonneg_right h1 hNf_pow_pos.le
          linarith
      _ ≤ ((M₂ : ℝ) * (d : ℝ) ^ K_tot) * (1 / (2 : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_right hcoef_le (by positivity)
      _ ≤ ((2 : ℝ) ^ d / 4) * (1 / (2 : ℝ) ^ d) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 4 := by
          have h2d_ne : ((2 : ℝ) ^ d) ≠ 0 := by positivity
          field_simp [h2d_ne]
  have herr_d := mul_le_mul_of_nonneg_right (hd_err d hd_e) hNf_pow_pos.le
  have hsum_le : err_fn d * (Nf d : ℝ) ^ c ≤ 1 := by
    have hsplit : (2 * (D d : ℝ) * (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d +
        ((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
        2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) * (Nf d : ℝ) ^ c =
        (2 * (D d : ℝ) * (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d)) * (Nf d : ℝ) ^ c +
        (2 * (D d : ℝ) * (((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
        2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) * (Nf d : ℝ) ^ c := by ring
    linarith [herr_d, hsplit, hterm1, hterm2]
  exact (le_div_iff₀ hNf_pow_pos).mpr (by linarith)

/-- Pure mathematical, combinatorial, total-variation, and asymptotic components for
`CritWinSpin.p4c_theorem_1_1_ii_from_theorem_7_2`:
(1) existence of gadget parameters `(Ac, Cc)` for any `p ≥ 2`, `w ≥ 1`, `ε ∈ (0, d_p)`;
(2) polynomial boundedness and `d ≤ Nf d` for the lifted instance size `Nf d = (n₀ d + 1) * cloudSize p Cc (n₀ d + 1)`;
(3) uniform polynomial bounds `D d = d^E + D₀` and `T d = CT * d^(2E) + CT` dominating `k d` and `⌈Ccap * (D d + 1 + n d^2)⌉₊`;
(4) zero-instance spectral and width bounds (`d < d₁` fallback);
(5) `keyLiftLaw` probability nonnegativity and normalization;
(6) prefix-sampling marginalization and TV convexity bound for `errExtKernel`: `1 - errExt(K_small) ≤ 2 D (1 - errExt(K_big))`;
(7) prefix-sampling padding and TV convexity bound for `errAmpKernel`: `1 - errAmp(K_small) ≤ 2 D (1 - errAmp(K_big))`;
(8) negligible closure of the Theorem 7.2 security bound against `1 / (Nf d)^c`;
(9) `InstLaw` perturbation bounds for `errExtKernel` and `errAmpKernel`. -/
private theorem p4c11_asymptotics_core :
    (∀ (p : ℕ) (_hp : 2 ≤ p) (w ε : ℝ), 1 ≤ w → 0 < ε → ε < dExp p →
      ∃ Ac Cc : ℕ, GadgetParams p w ε Ac Cc) ∧
    (∀ (p : ℕ) (n₀ : ℕ → ℕ), PolyBounded n₀ → (∀ d, d ^ 2 ≤ n₀ d) → ∀ Cc : ℕ,
      (∀ d, d ≤ (n₀ d + 1) * cloudSize p Cc (n₀ d + 1)) ∧
      PolyBounded (fun d => (n₀ d + 1) * cloudSize p Cc (n₀ d + 1))) ∧
    (∀ (k n : ℕ → ℕ), PolyBounded k → PolyBounded n → ∀ Ccap : ℝ, 0 < Ccap →
      ∃ E D₀ CT : ℕ, 1 ≤ E ∧ 1 ≤ D₀ ∧ 1 ≤ CT ∧
        (∀ d, 1 ≤ d ^ E + D₀ ∧ k d ≤ d ^ E + D₀) ∧
        (∀ d, 1 ≤ CT * d ^ (2 * E) + CT ∧
          ⌈Ccap * (((d ^ E + D₀ : ℕ) : ℝ) + 1 + (n d : ℝ) ^ 2)⌉₊ ≤ CT * d ^ (2 * E) + CT)) ∧
    (∀ (S : SpinLaw) (p N : ℕ) (ε Cρ : ℝ), 0 < Cρ →
      let I : Inst N := (0, 0)
      I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
        ((tau S * (1 + (N : ℝ) ^ (-dExp p + ε))) •
            (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef ∧
        width (castM I.1) (castV I.2) ≤ Cρ) ∧
    (∀ (F : BilinearFamily) (d : ℕ), 1 ≤ d → ∀ {N : ℕ} (f : (desc : Str) → WatersKey F desc d → Inst N),
      (∀ M ∈ (keyLiftLaw F d f).supp, 0 ≤ (keyLiftLaw F d f).prob M) ∧
      ∑ M ∈ (keyLiftLaw F d f).supp, (keyLiftLaw F d f).prob M = 1) ∧
    (∀ (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D) (Pi₀ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∑ M ∈ Pi₀.supp, Pi₀.prob M = 1) →
      ∀ (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ K_small M X o) → (∀ M X, ∑ o, K_small M X o = 1) →
      ∀ (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ R_rem M X o) → (∀ M X, ∑ o, R_rem M X o = 1) →
      ∀ w : ℝ, 1 / (2 * (D : ℝ)) ≤ w → w ≤ 1 →
      (∀ M X o, K_big M X o = w * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) o +
        (1 - w) * R_rem M X o) →
      1 - errExtKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errExtKernel S Pi₀ K_big)) ∧
    (∀ (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D) (Pi₀ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∑ M ∈ Pi₀.supp, Pi₀.prob M = 1) →
      ∀ (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ K_small M X o) → (∀ M X, ∑ o, K_small M X o = 1) →
      ∀ (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Fin (D + 1) → Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ R_rem M X o) → (∀ M X, ∑ o, R_rem M X o = 1) →
      ∀ w : ℝ, 1 / (2 * (D : ℝ)) ≤ w → w ≤ 1 →
      (∀ M (X : Fin D → Config S (Fin N)) o,
        K_big M X o = w * ∑ y : Option (Fin (k + 1) → Config S (Fin N)),
            (if Option.map (fun Y (j : Fin (D + 1)) =>
                if h : j.1 < k + 1 then Y ⟨j.1, h⟩ else X ⟨k + (j.1 - (k + 1)), by omega⟩) y = o
              then (1 : ℝ) else 0) * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) y +
          (1 - w) * R_rem M X o) →
      1 - errAmpKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errAmpKernel S Pi₀ K_big)) ∧
    (∀ (Nf D T n₀ : ℕ → ℕ) (v₁ v₂ err_fn : ℕ → ℝ) (C Cv : ℝ), 0 < C → 0 ≤ Cv →
      ∀ (F : BilinearFamily) (B : PPT), CDH F →
      (∀ d, d ≤ Nf d) → PolyBounded Nf → PolyBounded D → PolyBounded T → (∀ d, d ^ 2 ≤ n₀ d) →
      (∀ d, v₁ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2))) →
      (∀ d, v₂ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2))) →
      (∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 2 * (D d : ℝ) *
        (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d +
          ((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
          2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) →
      ∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 1 / (Nf d : ℝ) ^ c) ∧
    (∀ (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) →
      Pi₁.supp ⊆ Pi₀.supp → (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) →
      ∀ K : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ,
        (∀ M X o, 0 ≤ K M X o) → (∀ M X, ∑ o, K M X o = 1) →
        errExtKernel S Pi₀ K - errExtKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M|) ∧
    (∀ (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) →
      Pi₁.supp ⊆ Pi₀.supp → (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) →
      ∀ K : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ,
        (∀ M X o, 0 ≤ K M X o) → (∀ M X, ∑ o, K M X o = 1) →
        errAmpKernel S Pi₀ K - errAmpKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M|) :=
  ⟨fun p hp w ε hw hε hεd => p4c11_gadget_params p hp w ε hw hε hεd,
   fun p n₀ hn₀ hn₀_sq Cc => p4c11_Nf_bounds p n₀ hn₀ hn₀_sq Cc,
   fun k n hk hn Ccap hCcap => p4c11_poly_bounds k n hk hn Ccap hCcap,
   fun S p N ε Cρ hCρ => p4c11_zero_inst_props S p N ε Cρ hCρ,
   fun F d hd N f => p4c11_keyLiftLaw_valid F d hd f,
   fun S N k D hkD hD1 Pi₀ hPi0 hPi1 K_s hKs0 hKs1 K_b R_r hRr0 hRr1 w hw0 hw1 hm =>
     p4c11_prefix_mixture_bound_ext S N k D hkD hD1 Pi₀ hPi0 hPi1 K_s hKs0 hKs1 K_b R_r hRr0 hRr1 w hw0 hw1 hm,
   fun S N k D hkD hD1 Pi₀ hPi0 hPi1 K_s hKs0 hKs1 K_b R_r hRr0 hRr1 w hw0 hw1 hm =>
     p4c11_prefix_mixture_bound_amp S N k D hkD hD1 Pi₀ hPi0 hPi1 K_s hKs0 hKs1 K_b R_r hRr0 hRr1 w hw0 hw1 hm,
   fun Nf D T n₀ v₁ v₂ err_fn C Cv hC hCv F B hCDH hNf_le hNf_p hD_p hT_p hn₀ hv₁ hv₂ herr =>
     p4c11_negligible_closure Nf D T n₀ v₁ v₂ err_fn C Cv hC hCv F B hCDH hNf_le hNf_p hD_p hT_p hn₀ hv₁ hv₂ herr,
   fun S N k Pi₀ Pi₁ h0 h1 hs hz K hK0 hK1 => p4c11_instLaw_shift_ext S N k Pi₀ Pi₁ h0 h1 hs hz K hK0 hK1,
   fun S N k Pi₀ Pi₁ h0 h1 hs hz K hK0 hK1 => p4c11_instLaw_shift_amp S N k Pi₀ Pi₁ h0 h1 hs hz K hK0 hK1⟩

end CritWinSpin

open CritWinSpin

theorem solution :
    (∀ (p : ℕ) (_hp : 2 ≤ p) (w ε : ℝ), 1 ≤ w → 0 < ε → ε < dExp p →
      ∃ Ac Cc : ℕ, GadgetParams p w ε Ac Cc) ∧
    (∀ (p : ℕ) (n₀ : ℕ → ℕ), PolyBounded n₀ → (∀ d, d ^ 2 ≤ n₀ d) → ∀ Cc : ℕ,
      (∀ d, d ≤ (n₀ d + 1) * cloudSize p Cc (n₀ d + 1)) ∧
      PolyBounded (fun d => (n₀ d + 1) * cloudSize p Cc (n₀ d + 1))) ∧
    (∀ (k n : ℕ → ℕ), PolyBounded k → PolyBounded n → ∀ Ccap : ℝ, 0 < Ccap →
      ∃ E D₀ CT : ℕ, 1 ≤ E ∧ 1 ≤ D₀ ∧ 1 ≤ CT ∧
        (∀ d, 1 ≤ d ^ E + D₀ ∧ k d ≤ d ^ E + D₀) ∧
        (∀ d, 1 ≤ CT * d ^ (2 * E) + CT ∧
          ⌈Ccap * (((d ^ E + D₀ : ℕ) : ℝ) + 1 + (n d : ℝ) ^ 2)⌉₊ ≤ CT * d ^ (2 * E) + CT)) ∧
    (∀ (S : SpinLaw) (p N : ℕ) (ε Cρ : ℝ), 0 < Cρ →
      let I : Inst N := (0, 0)
      I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
        ((tau S * (1 + (N : ℝ) ^ (-dExp p + ε))) •
            (1 : Matrix (Fin N) (Fin N) ℝ) - castM I.1).PosSemidef ∧
        width (castM I.1) (castV I.2) ≤ Cρ) ∧
    (∀ (F : BilinearFamily) (d : ℕ), 1 ≤ d → ∀ {N : ℕ} (f : (desc : Str) → WatersKey F desc d → Inst N),
      (∀ M ∈ (keyLiftLaw F d f).supp, 0 ≤ (keyLiftLaw F d f).prob M) ∧
      ∑ M ∈ (keyLiftLaw F d f).supp, (keyLiftLaw F d f).prob M = 1) ∧
    (∀ (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D) (Pi₀ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∑ M ∈ Pi₀.supp, Pi₀.prob M = 1) →
      ∀ (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ K_small M X o) → (∀ M X, ∑ o, K_small M X o = 1) →
      ∀ (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ R_rem M X o) → (∀ M X, ∑ o, R_rem M X o = 1) →
      ∀ w : ℝ, 1 / (2 * (D : ℝ)) ≤ w → w ≤ 1 →
      (∀ M X o, K_big M X o = w * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) o +
        (1 - w) * R_rem M X o) →
      1 - errExtKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errExtKernel S Pi₀ K_big)) ∧
    (∀ (S : SpinLaw) (N k D : ℕ) (hkD : k ≤ D) (hD1 : 1 ≤ D) (Pi₀ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∑ M ∈ Pi₀.supp, Pi₀.prob M = 1) →
      ∀ (K_small : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ K_small M X o) → (∀ M X, ∑ o, K_small M X o = 1) →
      ∀ (K_big R_rem : Inst N → (Fin D → Config S (Fin N)) → Option (Fin (D + 1) → Config S (Fin N)) → ℝ),
        (∀ M X o, 0 ≤ R_rem M X o) → (∀ M X, ∑ o, R_rem M X o = 1) →
      ∀ w : ℝ, 1 / (2 * (D : ℝ)) ≤ w → w ≤ 1 →
      (∀ M (X : Fin D → Config S (Fin N)) o,
        K_big M X o = w * ∑ y : Option (Fin (k + 1) → Config S (Fin N)),
            (if Option.map (fun Y (j : Fin (D + 1)) =>
                if h : j.1 < k + 1 then Y ⟨j.1, h⟩ else X ⟨k + (j.1 - (k + 1)), by omega⟩) y = o
              then (1 : ℝ) else 0) * K_small M (fun j => X ⟨j.1, lt_of_lt_of_le j.2 hkD⟩) y +
          (1 - w) * R_rem M X o) →
      1 - errAmpKernel S Pi₀ K_small ≤ 2 * (D : ℝ) * (1 - errAmpKernel S Pi₀ K_big)) ∧
    (∀ (Nf D T n₀ : ℕ → ℕ) (v₁ v₂ err_fn : ℕ → ℝ) (C Cv : ℝ), 0 < C → 0 ≤ Cv →
      ∀ (F : BilinearFamily) (B : PPT), CDH F →
      (∀ d, d ≤ Nf d) → PolyBounded Nf → PolyBounded D → PolyBounded T → (∀ d, d ^ 2 ≤ n₀ d) →
      (∀ d, v₁ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2))) →
      (∀ d, v₂ d ≤ Cv * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2))) →
      (∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 2 * (D d : ℝ) *
        (C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d +
          ((T d : ℝ) + ((T d).choose 2 : ℝ) + 1) * (1 / (2 : ℝ) ^ d) +
          2 * (T d : ℝ) * Real.exp (-((n₀ d : ℝ) ^ 2)) + v₁ d + v₂ d)) →
      ∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀, err_fn d ≤ 1 / (Nf d : ℝ) ^ c) ∧
    (∀ (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) →
      Pi₁.supp ⊆ Pi₀.supp → (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) →
      ∀ K : Inst N → (Fin k → Config S (Fin N)) → Option (Config S (Fin N)) → ℝ,
        (∀ M X o, 0 ≤ K M X o) → (∀ M X, ∑ o, K M X o = 1) →
        errExtKernel S Pi₀ K - errExtKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M|) ∧
    (∀ (S : SpinLaw) (N k : ℕ) (Pi₀ Pi₁ : InstLaw N),
      (∀ M ∈ Pi₀.supp, 0 ≤ Pi₀.prob M) → (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) →
      Pi₁.supp ⊆ Pi₀.supp → (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) →
      ∀ K : Inst N → (Fin k → Config S (Fin N)) → Option (Fin (k + 1) → Config S (Fin N)) → ℝ,
        (∀ M X o, 0 ≤ K M X o) → (∀ M X, ∑ o, K M X o = 1) →
        errAmpKernel S Pi₀ K - errAmpKernel S Pi₁ K ≤ ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M|) :=
  p4c11_asymptotics_core

