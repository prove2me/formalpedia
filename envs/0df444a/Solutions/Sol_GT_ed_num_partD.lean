-- Prove2me | solution 1 for GT.ed_num_partD
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:37:07.627334+00:00
-- url     : https://prove2.me/submissions/271e6c59-77ff-470d-856c-fdbb5e7ee65d

import Mathlib
import Definitions.Def_GreenTaoFourCore

section File_GT_BadEdNum
/-!
# Theorem 6.6, the quadratic case: the numerical bookkeeping
-/

open Finset KM

namespace GT

noncomputable section

section edaux

set_option exponentiation.threshold 2048

variable {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
include hη0 hη1

lemma ed_Y : (10 : ℝ) ≤ 1 / η := by
  rw [le_div_iff₀ hη0]; linarith

lemma ed_Y1 : (1 : ℝ) ≤ 1 / η := le_trans (by norm_num) (ed_Y hη0 hη1)

lemma ed_J : u3J (edηi η) = (64 * (1 / η)) ^ (2 ^ 27) := by
  unfold u3J u3EJ edηi
  have e : 1 / (η / 16 / 4) ^ 8 = (64 * (1 / η)) ^ 8 := by field_simp; norm_num
  rw [e, ← pow_mul]; norm_num

lemma ed_J_ge : (1 / η) ^ (2 ^ 27) ≤ u3J (edηi η) := by
  rw [ed_J hη0 hη1]
  exact pow_le_pow_left₀ (by positivity) (by linarith [ed_Y hη0 hη1]) _

lemma ed_64 : 64 * (1 / η) ≤ (1 / η) ^ 3 := by
  have hY := ed_Y hη0 hη1
  have : (64 : ℝ) ≤ (1 / η) ^ 2 := by nlinarith
  calc 64 * (1 / η) ≤ (1 / η) ^ 2 * (1 / η) := by gcongr
    _ = (1 / η) ^ 3 := by ring

lemma ed_J_le : u3J (edηi η) ≤ (1 / η) ^ C2 := by
  rw [ed_J hη0 hη1]
  calc (64 * (1 / η)) ^ (2 ^ 27) ≤ ((1 / η) ^ 3) ^ (2 ^ 27) :=
        pow_le_pow_left₀ (by positivity) (ed_64 hη0 hη1) _
    _ = (1 / η) ^ (3 * 2 ^ 27) := by rw [← pow_mul]
    _ ≤ (1 / η) ^ C2 := pow_le_pow_right₀ (ed_Y1 hη0 hη1) (by unfold C2; norm_num)

lemma ed_logY : Real.log (1 / η) ≤ 1 / η := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 / η by positivity); linarith

lemma ed_pow_exp (k : ℕ) : (1 / η) ^ k = Real.exp (k * Real.log (1 / η)) := by
  rw [Real.exp_nat_mul, Real.exp_log (by positivity)]

lemma ed_eta_pow (k : ℕ) : η ^ k = Real.exp (-(k * Real.log (1 / η))) := by
  rw [Real.exp_neg, ← ed_pow_exp hη0 hη1, one_div, inv_pow, inv_inv]

variable {s : ℕ} (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
include hs

/-- The depth parameter `D = s + J + 1`. -/
lemma ed_D_ge : (1 / η) ^ (2 ^ 27) ≤ (s : ℝ) + u3J (edηi η) + 1 := by
  have := ed_J_ge hη0 hη1; have : (0 : ℝ) ≤ s := by positivity
  linarith

lemma ed_D_le : (s : ℝ) + u3J (edηi η) + 1 ≤ (1 / η) ^ (3 * C2 + 2) := by
  have hJ := ed_J_le hη0 hη1
  have hY := ed_Y hη0 hη1
  have hY1 := ed_Y1 hη0 hη1
  have h1 : (1 / η) ^ C2 ≤ (1 / η) ^ (3 * C2) := pow_le_pow_right₀ hY1 (by unfold C2; norm_num)
  have h2 : (1 : ℝ) ≤ (1 / η) ^ (3 * C2) := one_le_pow₀ hY1
  have h3 : (67 : ℝ) ≤ (1 / η) ^ 2 := by nlinarith
  rw [pow_add]
  have : 0 ≤ (1 / η) ^ (3 * C2) := by positivity
  nlinarith

lemma ed_D_big : (2 : ℝ) ^ 100 ≤ (s : ℝ) + u3J (edηi η) + 1 := by
  refine le_trans ?_ (ed_D_ge hη0 hη1 hs)
  calc (2 : ℝ) ^ 100 ≤ 10 ^ 100 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ (1 / η) ^ 100 := pow_le_pow_left₀ (by norm_num) (ed_Y hη0 hη1) _
    _ ≤ _ := pow_le_pow_right₀ (ed_Y1 hη0 hη1) (by norm_num)

lemma ed_D_Y : 1 / η ≤ (s : ℝ) + u3J (edηi η) + 1 := by
  refine le_trans ?_ (ed_D_ge hη0 hη1 hs)
  calc 1 / η = (1 / η) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (ed_Y1 hη0 hη1) (by norm_num)

/-- The smallness of `θ`. -/
lemma ed_theta_mul {M : ℝ} (hM0 : 0 ≤ M)
    (hM : M ≤ Real.exp (2 * ((s : ℝ) + u3J (edηi η) + 1) ^ 3)) :
    edθ s η * M ≤ Real.exp (-((s : ℝ) + u3J (edηi η) + 1) ^ 3) := by
  set D := (s : ℝ) + u3J (edηi η) + 1 with hD
  have hDb := ed_D_big hη0 hη1 hs
  have hD3 : (3 : ℝ) ≤ D := le_trans (by norm_num) hDb
  unfold edθ u3θ
  rw [← hD]
  calc Real.exp (-D ^ 4) * M ≤ Real.exp (-D ^ 4) * Real.exp (2 * D ^ 3) := by gcongr
    _ = Real.exp (-D ^ 4 + 2 * D ^ 3) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-D ^ 3) := by
      apply Real.exp_le_exp.2
      have h3 : 0 ≤ D ^ 3 := by positivity
      have : 3 * D ^ 3 ≤ D ^ 4 := by
        rw [show D ^ 4 = D * D ^ 3 by ring]; exact mul_le_mul_of_nonneg_right hD3 h3
      linarith

lemma ed_eps_le (k : ℕ) (hk : k ≤ 2 ^ 65) :
    Real.exp (-((s : ℝ) + u3J (edηi η) + 1) ^ 3) ≤ η ^ k := by
  set D := (s : ℝ) + u3J (edηi η) + 1 with hD
  rw [ed_eta_pow hη0 hη1]
  apply Real.exp_le_exp.2
  have hDb := ed_D_big hη0 hη1 hs
  have hDY := ed_D_Y hη0 hη1 hs
  have hL := ed_logY hη0 hη1
  have hL0 : 0 ≤ Real.log (1 / η) := Real.log_nonneg (ed_Y1 hη0 hη1)
  have hk' : (k : ℝ) ≤ 2 ^ 65 := by exact_mod_cast hk
  have hD1 : (1 : ℝ) ≤ D := le_trans (by norm_num) hDb
  have h1 : (k : ℝ) * Real.log (1 / η) ≤ 2 ^ 65 * D := by
    have : (k : ℝ) * Real.log (1 / η) ≤ 2 ^ 65 * (1 / η) :=
      mul_le_mul hk' hL hL0 (by norm_num)
    linarith [mul_le_mul_of_nonneg_left hDY (show (0 : ℝ) ≤ 2 ^ 65 by norm_num)]
  have h2 : 2 ^ 65 * D ≤ D ^ 3 := by
    have : (2 : ℝ) ^ 65 ≤ D ^ 2 := by
      have : (2 : ℝ) ^ 65 ≤ 2 ^ 100 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      nlinarith
    calc 2 ^ 65 * D ≤ D ^ 2 * D := mul_le_mul_of_nonneg_right this (by linarith)
      _ = D ^ 3 := by ring
  linarith

lemma ed_M_le {x c : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (s : ℝ) + u3J (edηi η) + 1) (hc0 : 0 ≤ c)
    (hc : c ≤ 2 ^ 64) : c * x ≤ Real.exp (((s : ℝ) + u3J (edηi η) + 1) ^ 3) := by
  set D := (s : ℝ) + u3J (edηi η) + 1 with hD
  have hDb := ed_D_big hη0 hη1 hs
  have hc' : c ≤ D := hc.trans (le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hDb)
  have hD1 : (1 : ℝ) ≤ D := le_trans (by norm_num) hDb
  calc c * x ≤ D * D := mul_le_mul hc' hx hx0 (by linarith)
    _ ≤ D ^ 3 := by nlinarith
    _ ≤ Real.exp (D ^ 3) := by have := Real.add_one_le_exp (D ^ 3); linarith

lemma ed_M_le2 {x c : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (s : ℝ) + u3J (edηi η) + 1) (hc0 : 0 ≤ c)
    (hc : c ≤ 2 ^ 64) : c * x ≤ Real.exp (2 * ((s : ℝ) + u3J (edηi η) + 1) ^ 3) := by
  refine (ed_M_le hη0 hη1 hs hx0 hx hc0 hc).trans (Real.exp_le_exp.2 ?_)
  have : 0 ≤ ((s : ℝ) + u3J (edηi η) + 1) ^ 3 :=
    pow_nonneg (le_trans (by positivity) (ed_D_big hη0 hη1 hs)) 3
  linarith

end edaux

set_option exponentiation.threshold 2048 in
set_option maxHeartbeats 8000000 in
theorem ed_num_partD {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t d2 : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd2 : (d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) :
    (6 * edK s η < p) ∧
    (4 * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ≤ edθ s η * SLA.eps4 η * ρ) ∧
    (24 * (edθ s η * SLA.eps4 η * ρ) ≤ ρ / 2) ∧
    (16 * 2 ^ d2 ≤ Real.exp ((1 / η) ^ C3)) ∧
    (4 * edE η + η ^ C2 ≤ 3 * edκ η ^ 2 * (η / 16 / 4 * (η / 16))) := by
  have hY := ed_Y hη0 hη1
  have hY1 := ed_Y1 hη0 hη1
  have hYp : ∀ {a b : ℕ}, a ≤ b → (1 / η) ^ a ≤ (1 / η) ^ b := fun h => pow_le_pow_right₀ hY1 h
  set D := (s : ℝ) + u3J (edηi η) + 1 with hD
  have hθe0 : edθ s η = Real.exp (-D ^ 4) := rfl
  have hKe0 : edK s η = Real.exp (D ^ 3) := rfl
  have hDb : (2 : ℝ) ^ 100 ≤ D := ed_D_big hη0 hη1 hs
  have hDle : D ≤ (1 / η) ^ (3 * C2 + 2) := ed_D_le hη0 hη1 hs
  have hDY : 1 / η ≤ D := ed_D_Y hη0 hη1 hs
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDb
  have hJ0 : 0 ≤ u3J (edηi η) := le_trans (by positivity) (ed_J_ge hη0 hη1)
  have hsD : (s : ℝ) ≤ D := by rw [hD]; linarith
  have htD : (t : ℝ) ≤ D := le_trans (by exact_mod_cast hts) hsD
  set θ := edθ s η with hθdef
  have hθe : θ = Real.exp (-D ^ 4) := hθe0
  have hθ0 : 0 < θ := by rw [hθe]; exact Real.exp_pos _
  set E := Real.exp (-D ^ 3) with hE
  have hEk : ∀ k : ℕ, k ≤ 2 ^ 65 → E ≤ η ^ k := fun k hk => ed_eps_le hη0 hη1 hs k hk
  have hθM : ∀ {M : ℝ}, 0 ≤ M → M ≤ Real.exp (2 * D ^ 3) → θ * M ≤ E :=
    fun h0 h => ed_theta_mul hη0 hη1 hs h0 h
  have hM2 : ∀ {x c : ℝ}, 0 ≤ x → x ≤ D → 0 ≤ c → c ≤ 2 ^ 64 → c * x ≤ Real.exp (2 * D ^ 3) :=
    fun hx0 hx hc0 hc => ed_M_le2 hη0 hη1 hs hx0 hx hc0 hc
  have hM1 : ∀ {x c : ℝ}, 0 ≤ x → x ≤ D → 0 ≤ c → c ≤ 2 ^ 64 → c * x ≤ Real.exp (D ^ 3) :=
    fun hx0 hx hc0 hc => ed_M_le hη0 hη1 hs hx0 hx hc0 hc
  clear_value D
  have hηk : ∀ k : ℕ, η ^ (k + 1) ≤ η * (1 / 10) ^ k := fun k => by
    rw [pow_succ']; gcongr
  have hE2 : E ≤ 1 / 100 := by
    have := hEk 2 (by norm_num)
    have : η ^ 2 ≤ (1 / 10) ^ 2 := pow_le_pow_left₀ hη0.le hη1 2
    linarith [show ((1 : ℝ) / 10) ^ 2 = 1 / 100 by norm_num]
  have hθs : θ ≤ 1 / 100 := by
    have := hθM (M := 1) (by norm_num) (by
      have := Real.add_one_le_exp (2 * D ^ 3); have : 0 ≤ D ^ 3 := by positivity
      linarith)
    linarith
  have hθ1 : θ ≤ 1 := by linarith
  -- `eps4`
  set ep := SLA.eps4 η with hepdef
  have hep : ep = Real.exp (-(1 / η) ^ C4) := rfl
  have hep0 : 0 < ep := by rw [hep]; exact Real.exp_pos _
  have hepθ : ep ≤ θ := by
    rw [hep, hθe]
    apply Real.exp_le_exp.2
    have : D ^ 4 ≤ (1 / η) ^ C4 := by
      calc D ^ 4 ≤ ((1 / η) ^ (3 * C2 + 2)) ^ 4 := pow_le_pow_left₀ hD0.le hDle 4
        _ = (1 / η) ^ ((3 * C2 + 2) * 4) := by rw [← pow_mul]
        _ ≤ _ := hYp (by unfold C2 C4; norm_num)
    linarith
  have hep1 : ep ≤ 1 := hepθ.trans hθ1
  have hρp : 0 < ρ := lt_of_lt_of_le (Real.exp_pos _) hρ0
  -- the depth
  set T' := edT η with hT'
  have hT'1 : 1 ≤ T' := by show 1 ≤ u3T (edηi η); unfold u3T; omega
  have hT'D : (T' : ℝ) + 1 ≤ 121 * D := by
    show ((u3T (edηi η) : ℕ) : ℝ) + 1 ≤ 121 * D
    unfold u3T; push_cast
    have := Nat.floor_le hJ0
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have : u3J (edηi η) ≤ D := by rw [hD]; linarith
    have : (1 : ℝ) ≤ D := le_trans (by norm_num) hDb
    linarith
  have hθT : θ ^ T' ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by omega)
  have hθT0 : 0 < θ ^ T' := by positivity
  set K := edK s η with hKdef
  have hKe : K = Real.exp (D ^ 3) := hKe0
  have hK1 : 1 ≤ K := by rw [hKe]; exact Real.one_le_exp (pow_nonneg hD0.le 3)
  have hD3 : (4 : ℝ) ≤ D ^ 3 := by
    have : (4 : ℝ) ≤ D := le_trans (by norm_num) hDb
    exact this.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hK4 : 12 ≤ K := by
    rw [hKe]; have := Real.add_one_le_exp (D ^ 3)
    have : (12 : ℝ) ≤ D ^ 3 + 1 := by
      have : (12 : ℝ) ≤ D := le_trans (by norm_num) hDb
      linarith [this.trans (le_self_pow₀ (by linarith) (by norm_num) : D ≤ D ^ 3)]
    linarith
  have hKM : ∀ {c x : ℝ}, 0 ≤ x → x ≤ D → 0 ≤ c → c ≤ 2 ^ 64 →
      c * x * K ≤ Real.exp (2 * D ^ 3) := fun hx0 hx hc0 hc => by
    have := hM1 hx0 hx hc0 hc
    rw [hKe, show 2 * D ^ 3 = D ^ 3 + D ^ 3 by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  -- the `θ^T'` lower bound
  have hθTlow : Real.exp (-(1 / η) ^ C5) ≤ θ ^ T' * θ * ep := by
    have e : θ ^ T' * θ * ep = Real.exp (-(((T' : ℝ) + 1) * D ^ 4 + (1 / η) ^ C4)) := by
      rw [hθe, hep, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e]
    apply Real.exp_le_exp.2
    have h1 : ((T' : ℝ) + 1) * D ^ 4 ≤ (1 / η) ^ C4 := by
      have h121 : (121 : ℝ) ≤ (1 / η) ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hY 3)
      calc ((T' : ℝ) + 1) * D ^ 4 ≤ (121 * D) * D ^ 4 := by gcongr
        _ = 121 * D ^ 5 := by ring
        _ ≤ (1 / η) ^ 3 * ((1 / η) ^ (3 * C2 + 2)) ^ 5 := by gcongr
        _ = (1 / η) ^ (3 + (3 * C2 + 2) * 5) := by rw [← pow_mul, ← pow_add]
        _ ≤ _ := hYp (by unfold C2 C4; norm_num)
    have h2 : 2 * (1 / η) ^ C4 ≤ (1 / η) ^ C5 := by
      calc 2 * (1 / η) ^ C4 ≤ (1 / η) * (1 / η) ^ C4 := by gcongr; linarith
        _ = (1 / η) ^ (C4 + 1) := by ring
        _ ≤ _ := hYp (by unfold C4 C5; norm_num)
    linarith
  refine ⟨?kp, ?e2, ?e3, ?vol, ?ndec⟩
  case kp =>
    have h6 : 6 * K ≤ Real.exp (2 * D ^ 3) := by
      rw [hKe, show 2 * D ^ 3 = D ^ 3 + D ^ 3 by ring, Real.exp_add]
      have : (6 : ℝ) ≤ Real.exp (D ^ 3) := by
        have := Real.add_one_le_exp (D ^ 3); linarith
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    have hlt : Real.exp (2 * D ^ 3) < Real.exp ((1 / η) ^ (3 * C5)) := by
      apply Real.exp_lt_exp.2
      have h1 : D ^ 3 ≤ (1 / η) ^ ((3 * C2 + 2) * 3) := by
        rw [pow_mul]; exact pow_le_pow_left₀ hD0.le hDle 3
      have h2 : 2 * (1 / η) ^ ((3 * C2 + 2) * 3) < (1 / η) ^ (3 * C5) := by
        calc 2 * (1 / η) ^ ((3 * C2 + 2) * 3) < (1 / η) * (1 / η) ^ ((3 * C2 + 2) * 3) := by
              gcongr; linarith
          _ = (1 / η) ^ ((3 * C2 + 2) * 3 + 1) := by ring
          _ ≤ _ := hYp (by unfold C2 C5; norm_num)
      linarith
    linarith
  case e2 =>
    have h := hθM (M := 4 * K) (by positivity) (by
      rw [hKe, show 2 * D ^ 3 = D ^ 3 + D ^ 3 by ring, Real.exp_add]
      have : (4 : ℝ) ≤ Real.exp (D ^ 3) := by have := Real.add_one_le_exp (D ^ 3); linarith
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le)
    have h2 : 4 * K * θ ^ T' ≤ 1 := by
      have : 4 * K * θ ^ T' ≤ θ * (4 * K) := by nlinarith
      linarith
    have hρ0' : 0 < θ * ep * ρ := by positivity
    nlinarith
  case e3 =>
    have : θ * ep ≤ θ := mul_le_of_le_one_right hθ0.le hep1
    nlinarith [mul_pos hθ0 hep0]
  case vol =>
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (16 : ℝ) * 2 ^ d2 = 2 ^ (4 + d2) := by rw [pow_add]; norm_num
      _ ≤ Real.exp 1 ^ (4 + d2) := pow_le_pow_left₀ (by norm_num) h2 _
      _ = Real.exp ((4 + d2 : ℕ) * 1) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((1 / η) ^ C3) := by
        apply Real.exp_le_exp.2
        push_cast
        have h64 : (64 : ℝ) ≤ (1 / η) ^ 2 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hY 2)
        have e1 : 64 * (1 / η) ^ (2 * C2) ≤ (1 / η) ^ (2 * C2 + 2) := by
          rw [pow_add]; nlinarith [show (0 : ℝ) ≤ (1 / η) ^ (2 * C2) by positivity]
        have e2 : (4 : ℝ) ≤ (1 / η) ^ (2 * C2 + 2) := by
          have : (1 : ℝ) ≤ (1 / η) ^ (2 * C2) := one_le_pow₀ hY1
          rw [pow_add]; nlinarith
        have e3 : 2 * (1 / η) ^ (2 * C2 + 2) ≤ (1 / η) ^ C3 := by
          calc 2 * (1 / η) ^ (2 * C2 + 2) ≤ (1 / η) * (1 / η) ^ (2 * C2 + 2) := by gcongr; linarith
            _ = (1 / η) ^ (2 * C2 + 3) := by ring
            _ ≤ _ := hYp (by unfold C2 C3; norm_num)
        linarith
  case ndec =>
    have eR : 3 * edκ η ^ 2 * (η / 16 / 4 * (η / 16)) = 12 * (η / 64) ^ (2 ^ 24 + 2) := by
      have hx : η / 16 / 4 = η / 64 := by ring
      have hx2 : η / 16 = 4 * (η / 64) := by ring
      unfold edκ u3κ edηi
      rw [hx, hx2]
      generalize η / 64 = x
      ring
    rw [eR]
    unfold edE
    have hC : η ^ C3 ≤ η ^ C2 := pow_le_pow_of_le_one hη0.le (by linarith) (by unfold C2 C3; norm_num)
    have key : η ^ C2 ≤ (η / 64) ^ (2 ^ 24 + 2) := by
      have e : η ^ C2 = η ^ (2 ^ 24 + 2) * η ^ (C2 - (2 ^ 24 + 2)) := by
        rw [← pow_add]; congr 1 <;> norm_num [C2]
      rw [e, div_pow]
      have h1 : η ^ (C2 - (2 ^ 24 + 2)) ≤ (1 / 2) ^ (C2 - (2 ^ 24 + 2)) :=
        pow_le_pow_left₀ hη0.le (by linarith) _
      have h2 : ((1 : ℝ) / 2) ^ (C2 - (2 ^ 24 + 2)) ≤ (1 / 2) ^ (6 * (2 ^ 24 + 2)) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num [C2])
      have h3 : ((1 : ℝ) / 2) ^ (6 * (2 ^ 24 + 2)) = 1 / 64 ^ (2 ^ 24 + 2) := by
        rw [pow_mul, one_div_pow, one_div_pow]; norm_num
      rw [h3] at h2
      have : 0 ≤ η ^ (2 ^ 24 + 2) := by positivity
      calc η ^ (2 ^ 24 + 2) * η ^ (C2 - (2 ^ 24 + 2)) ≤ η ^ (2 ^ 24 + 2) * (1 / 64 ^ (2 ^ 24 + 2)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) this
        _ = η ^ (2 ^ 24 + 2) / 64 ^ (2 ^ 24 + 2) := by ring
    have : 0 ≤ (η / 64) ^ (2 ^ 24 + 2) := by positivity
    generalize (η / 64) ^ (2 ^ 24 + 2) = X at key this ⊢
    generalize η ^ C2 = A at hC key ⊢
    generalize η ^ C3 = B at hC ⊢
    linarith

end

end GT
end File_GT_BadEdNum

open Finset KM
open GT in
theorem solution {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t d2 : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd2 : (d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) :
    (6 * edK s η < p) ∧
    (4 * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ≤ edθ s η * SLA.eps4 η * ρ) ∧
    (24 * (edθ s η * SLA.eps4 η * ρ) ≤ ρ / 2) ∧
    (16 * 2 ^ d2 ≤ Real.exp ((1 / η) ^ C3)) ∧
    (4 * edE η + η ^ C2 ≤ 3 * edκ η ^ 2 * (η / 16 / 4 * (η / 16))) :=
  @GT.ed_num_partD η hη0 hη1 s t d2 hts hs hd2 ρ hρ0 p hp

