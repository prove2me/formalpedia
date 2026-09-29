-- Prove2me | solution 1 for GT.ed_num
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:46.981539+00:00
-- url     : https://prove2.me/submissions/74747a0b-c441-4f5f-b061-7a0db955d03c

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_ed_num_partA
import Theorems.Thm_GT_ed_num_partD

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
theorem ed_num_partB {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) :
    (50 * (t : ℝ) * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) / (edθ s η * SLA.eps4 η * ρ) + 50 * (t : ℝ) * (6 * (edθ s η * SLA.eps4 η * ρ)) / (ρ / 2) ≤ edE η) := by
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
  refine ?e5
  case e5 =>
    have hr00 : 0 < θ * ep * ρ := by positivity
    have e1 : 50 * (t : ℝ) * (K * (θ ^ T' * (θ * ep * ρ))) / (θ * ep * ρ) =
        50 * t * K * θ ^ T' := by field_simp
    have e2 : 50 * (t : ℝ) * (6 * (θ * ep * ρ)) / (ρ / 2) = θ * (600 * t) * ep := by
      field_simp; ring
    rw [e1, e2]
    have h1 : 50 * t * K * θ ^ T' ≤ E := by
      have := hθM (M := 50 * t * K) (by positivity) (hKM (by positivity) htD (by norm_num)
        (by norm_num))
      have : 50 * t * K * θ ^ T' ≤ θ * (50 * t * K) := by
        have : 0 ≤ 50 * (t : ℝ) * K := by positivity
        nlinarith
      linarith
    have h2 : θ * (600 * t) * ep ≤ E := by
      have := hθM (M := 600 * t) (by positivity) (hM2 (by positivity) htD (by norm_num) (by norm_num))
      have : θ * (600 * t) * ep ≤ θ * (600 * t) := mul_le_of_le_one_right (by positivity) hep1
      linarith
    have h3 : E ≤ η ^ (C3 + 2) := hEk _ (by unfold C3; norm_num)
    have h4 : η ^ (C3 + 2) ≤ η ^ C3 / 4 := by
      rw [pow_add]
      have : η ^ 2 ≤ 1 / 4 := by nlinarith
      have : 0 ≤ η ^ C3 := by positivity
      nlinarith
    unfold edE
    linarith

set_option exponentiation.threshold 2048 in
set_option maxHeartbeats 8000000 in
theorem ed_num_partC {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) :
    (12 * (SLA.eps4 η * ρ) ≤ ρ / 2) ∧
    (72 * (edθ s η * SLA.eps4 η * ρ) ≤ SLA.eps4 η * ρ) ∧
    (6 * (edθ s η * SLA.eps4 η * ρ) + 12 * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ≤ ρ / 2) := by
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
  refine ⟨?n1, ?n5, ?e4⟩
  case n1 =>
    have : ep ≤ 1 / 100 := hepθ.trans hθs
    nlinarith
  case n5 =>
    have : 72 * θ ≤ 1 := by linarith
    nlinarith [mul_pos hep0 hρp]
  case e4 =>
    have h := hθM (M := 12 * K) (by positivity) (by
      rw [hKe, show 2 * D ^ 3 = D ^ 3 + D ^ 3 by ring, Real.exp_add]
      have : (12 : ℝ) ≤ Real.exp (D ^ 3) := by
        have := Real.add_one_le_exp (D ^ 3)
        have : (12 : ℝ) ≤ D := le_trans (by norm_num) hDb
        nlinarith
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le)
    have h2 : 12 * K * θ ^ T' ≤ 1 / 100 := by
      have : 12 * K * θ ^ T' ≤ θ * (12 * K) := by nlinarith
      linarith
    have hr0 : θ * ep * ρ ≤ ρ / 100 := by
      have : θ * ep ≤ 1 / 100 := (mul_le_of_le_one_right hθ0.le hep1).trans hθs
      nlinarith
    have hr00 : 0 < θ * ep * ρ := by positivity
    have : 12 * (K * (θ ^ T' * (θ * ep * ρ))) = (12 * K * θ ^ T') * (θ * ep * ρ) := by ring
    nlinarith

set_option exponentiation.threshold 2048 in
set_option maxHeartbeats 8000000 in
theorem ed_num_partE {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) (hρ1 : ρ ≤ 1) :
    (50 * (t : ℝ) * (3 * (SLA.eps4 η * ρ)) / (ρ / 2) ≤ η / 16 / 8) ∧
    (72 * (edθ s η * SLA.eps4 η * ρ) ≤ ρ / 2) ∧
    (50 * (t : ℝ) * (18 * (edθ s η * SLA.eps4 η * ρ)) / (ρ / 2) ≤ η / 16 / 16) ∧
    (50 * (t : ℝ) * (18 * (edθ s η * SLA.eps4 η * ρ)) / (SLA.eps4 η * ρ) ≤ η / 16 / 16) ∧
    (0 < edθ s η) ∧
    (edθ s η ≤ 1) ∧
    (0 < edηi η) ∧
    (edηi η ≤ 1 / 2 ^ 30) ∧
    (0 < edθ s η * SLA.eps4 η * ρ) ∧
    (edθ s η * SLA.eps4 η * ρ ≤ 1) ∧
    (1 ≤ edK s η) ∧
    (0 < edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ)) ∧
    (2 * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ)) ≤ 1) ∧
    (0 ≤ u3J (edηi η)) ∧
    (u3J (edηi η) ≤ (1 / η) ^ C2) ∧
    (Real.exp (-(1 / η) ^ C5) * ρ ≤ 2 * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ∧
    (0 ≤ edκ η) ∧
    (edκ η ≤ 1 / 4) ∧
    (edE η ≤ η ^ C3) := by
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
  refine ⟨?n2, ?n3, ?n4, ?n6, hθ0, hθ1, ?ηipos, ?ηile, by positivity, ?ρ0le, hK1, by positivity, ?e1, hJ0, ed_J_le hη0 hη1, ?rm, ?κ0, ?κ1, ?E1⟩
  case n2 =>
    have e : 50 * (t : ℝ) * (3 * (ep * ρ)) / (ρ / 2) = ep * (300 * t) := by field_simp; ring
    rw [e]
    have h1 : ep * (300 * t) ≤ θ * (300 * t) := by gcongr
    have h2 := hθM (M := 300 * t) (by positivity) (hM2 (by positivity) htD (by norm_num) (by norm_num))
    have h3 := hEk 8 (by norm_num)
    have h4 := hηk 7
    have : η * (1 / 10) ^ 7 ≤ η / 16 / 8 := by
      rw [show η / 16 / 8 = η * (1 / 128) by ring]; gcongr; norm_num
    linarith
  case n3 =>
    show 72 * (θ * ep * ρ) ≤ ρ / 2
    have : θ * ep ≤ 1 / 100 * (1 / 100) := mul_le_mul hθs (hepθ.trans hθs) hep0.le (by norm_num)
    have := mul_le_mul_of_nonneg_right this hρp.le
    linarith
  case n4 =>
    have e : 50 * (t : ℝ) * (18 * (θ * ep * ρ)) / (ρ / 2) = θ * (1800 * t) * ep := by
      field_simp; ring
    rw [e]
    have h2 := hθM (M := 1800 * t) (by positivity) (hM2 (by positivity) htD (by norm_num) (by norm_num))
    have h1 : θ * (1800 * t) * ep ≤ θ * (1800 * t) :=
      mul_le_of_le_one_right (by positivity) hep1
    have h3 := hEk 8 (by norm_num)
    have h4 := hηk 7
    have : η * (1 / 10) ^ 7 ≤ η / 16 / 16 := by
      rw [show η / 16 / 16 = η * (1 / 256) by ring]; gcongr; norm_num
    linarith
  case n6 =>
    have e : 50 * (t : ℝ) * (18 * (θ * ep * ρ)) / (ep * ρ) = θ * (900 * t) := by
      field_simp; ring
    rw [e]
    have h2 := hθM (M := 900 * t) (by positivity) (hM2 (by positivity) htD (by norm_num) (by norm_num))
    have h3 := hEk 8 (by norm_num)
    have h4 := hηk 7
    have : η * (1 / 10) ^ 7 ≤ η / 16 / 16 := by
      rw [show η / 16 / 16 = η * (1 / 256) by ring]; gcongr; norm_num
    linarith
  case ηipos => unfold edηi; positivity
  case ηile =>
    unfold edηi
    calc (η / 16 / 4) ^ 8 ≤ (1 / 10 / 16 / 4) ^ 8 := by gcongr
      _ ≤ 1 / 2 ^ 30 := by norm_num
  case ρ0le =>
    have : θ * ep ≤ 1 := mul_le_one₀ hθ1 hep0.le hep1
    calc θ * ep * ρ ≤ 1 * 1 := mul_le_mul this hρ1 hρp.le (by norm_num)
      _ = 1 := by ring
  case e1 =>
    have : θ ^ T' * (θ * ep * ρ) ≤ 1 / 100 := by
      have a1 : θ ^ T' ≤ 1 := hθT.trans hθ1
      have a2 : θ * ep * ρ ≤ 1 / 100 := by
        have : θ * ep ≤ θ := mul_le_of_le_one_right hθ0.le hep1
        nlinarith [mul_pos hθ0 hep0]
      calc θ ^ T' * (θ * ep * ρ) ≤ 1 * (1 / 100) := mul_le_mul a1 a2 (by positivity) (by norm_num)
        _ = 1 / 100 := by ring
    linarith
  case rm =>
    have : Real.exp (-(1 / η) ^ C5) * ρ ≤ θ ^ T' * θ * ep * ρ :=
      mul_le_mul_of_nonneg_right hθTlow hρp.le
    have h0 : 0 ≤ θ ^ T' * θ * ep * ρ := by positivity
    have e : θ ^ T' * (θ * ep * ρ) = θ ^ T' * θ * ep * ρ := by ring
    rw [e]; linarith
  case κ0 => unfold edκ u3κ edηi; positivity
  case κ1 =>
    unfold edκ u3κ
    have h1 : edηi η ≤ 1 / 4 := by
      unfold edηi
      calc (η / 16 / 4) ^ 8 ≤ (1 / 10 / 16 / 4) ^ 8 := by gcongr
        _ ≤ 1 / 4 := by norm_num
    have h0 : 0 ≤ edηi η := by unfold edηi; positivity
    exact (pow_le_of_le_one h0 (h1.trans (by norm_num)) (by norm_num)).trans h1
  case E1 =>
    unfold edE
    have : 0 ≤ η ^ C3 := by positivity
    linarith

theorem ed_num {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t d2 : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd2 : (d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) (hρ1 : ρ ≤ 1) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) : EdNum η s t d2 ρ p := by
  obtain f_pl := ed_num_partA hη0 hη1 hts hs hρ0 hρ1 hp
  obtain f_e5 := ed_num_partB hη0 hη1 hts hs hρ0
  obtain ⟨f_n1, f_n5, f_e4⟩ := ed_num_partC hη0 hη1 hts hs hρ0
  obtain ⟨f_kp, f_e2, f_e3, f_vol, f_dec⟩ := ed_num_partD hη0 hη1 hts hs hd2 hρ0 hp
  obtain ⟨f_n2, f_n3, f_n4, f_n6, f_θpos, f_θle, f_ηipos, f_ηile, f_ρ0pos, f_ρ0le, f_K1, f_e0, f_e1, f_J0, f_J1, f_rm, f_κ0, f_κ1, f_E1⟩ := ed_num_partE hη0 hη1 hts hs hρ0 hρ1
  exact ⟨f_n1, f_n2, f_n3, f_n4, f_n5, f_n6, f_θpos, f_θle, f_ηipos, f_ηile, f_ρ0pos, f_ρ0le, f_pl, f_kp, f_K1, f_e0, f_e1, f_e2, f_e3, f_e4, f_e5, f_J0, f_J1, f_rm, f_vol, f_κ0, f_κ1, f_dec, f_E1⟩

end

end GT
end File_GT_BadEdNum

open Finset KM
open GT in
theorem solution {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {s t d2 : ℕ} (hts : t ≤ s)
    (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd2 : (d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    {ρ : ℝ} (hρ0 : Real.exp (-(1 / η) ^ (2 * C5)) ≤ ρ) (hρ1 : ρ ≤ 1) {p : ℕ}
    (hp : Real.exp ((1 / η) ^ (3 * C5)) ≤ p) : EdNum η s t d2 ρ p :=
  @GT.ed_num η hη0 hη1 s t d2 hts hs hd2 ρ hρ0 hρ1 p hp

