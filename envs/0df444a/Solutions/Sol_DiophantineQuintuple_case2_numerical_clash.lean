-- Prove2me | solution 1 for DiophantineQuintuple.case2_numerical_clash
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-23T16:15:45.080477+00:00
-- url     : https://prove2.me/submissions/39f28e79-69df-4244-8153-866c3e3d0738

import Definitions.Def_diophantine_descent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false
open DiophantineDescent

theorem solution (b n : Nat) (hb : 0 < b)
    (hlo : (0.4553:ℝ) * (b : ℝ) < (n : ℝ))
    (hhi : (n : ℝ) < 18 * Real.log (227.712 * (b : ℝ))
        * Real.log (1.976 * (b : ℝ))
        / (Real.log (1.908 * (b : ℝ)) * Real.log (1.007 : ℝ))) :
    b < 97000 := by
  by_contra hcon
  push_neg at hcon
  have hbR : (97000:ℝ) ≤ (b:ℝ) := by exact_mod_cast hcon
  have hbpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have h1b : (1:ℝ) < (b:ℝ) := by linarith
  have h1ble : (1:ℝ) ≤ (b:ℝ) := by linarith
  -- Mathlib decimal bounds on e
  have egt : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have elt : Real.exp 1 < (2.7182818286:ℝ) := Real.exp_one_lt_d9
  have e5 : Real.exp (5:ℝ) = (Real.exp 1)^(5:ℕ) := by
    have h : (5:ℝ) = ((5:ℕ):ℝ) * 1 := by norm_num
    rw [h, Real.exp_nat_mul]
  have e11 : Real.exp (11:ℝ) = (Real.exp 1)^(11:ℕ) := by
    have h : (11:ℝ) = ((11:ℕ):ℝ) * 1 := by norm_num
    rw [h, Real.exp_nat_mul]
  -- upper bound exp y ≤ (1-y)⁻¹ for y ∈ [0,1), via exp(-y) ≥ 1-y
  have exp_upper : ∀ y : ℝ, 0 ≤ y → y < 1 → Real.exp y ≤ (1 - y)⁻¹ := by
    intro y hy0 hy1
    have h1 : (1:ℝ) - y ≤ Real.exp (-y) := by
      have h := Real.add_one_le_exp (-y)
      linarith
    have hpos : (0:ℝ) < 1 - y := by linarith
    have heq : Real.exp y = (Real.exp (-y))⁻¹ := by rw [Real.exp_neg, inv_inv]
    rw [heq]
    exact (inv_le_inv₀ (Real.exp_pos _) hpos).mpr h1
  -- (a) 0.006975 ≤ log 1.007
  have hlog1007 : (0.006975:ℝ) ≤ Real.log 1.007 := by
    have hexp : Real.exp (0.006975:ℝ) ≤ (1.007:ℝ) := by
      have h2 : Real.exp (0.006975:ℝ) = (Real.exp (0.000108984375:ℝ))^(64:ℕ) := by
        have h : (0.006975:ℝ) = ((64:ℕ):ℝ) * 0.000108984375 := by norm_num
        rw [h, Real.exp_nat_mul]
      have hub : Real.exp (0.000108984375:ℝ) ≤ (1 - 0.000108984375)⁻¹ :=
        exp_upper _ (by norm_num) (by norm_num)
      have h3 : (Real.exp (0.000108984375:ℝ))^(64:ℕ)
          ≤ ((1 - 0.000108984375)⁻¹)^(64:ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos _).le hub 64
      calc Real.exp (0.006975:ℝ) = (Real.exp (0.000108984375:ℝ))^(64:ℕ) := h2
        _ ≤ ((1 - 0.000108984375)⁻¹)^(64:ℕ) := h3
        _ ≤ 1.007 := by norm_num
    calc (0.006975:ℝ) = Real.log (Real.exp 0.006975) := (Real.log_exp _).symm
      _ ≤ Real.log 1.007 := Real.log_le_log (Real.exp_pos _) hexp
  -- (b) 0.645 ≤ log 1.908
  have hlog1908 : (0.645:ℝ) ≤ Real.log 1.908 := by
    have hexp : Real.exp (0.645:ℝ) ≤ (1.908:ℝ) := by
      have h2 : Real.exp (0.645:ℝ) = (Real.exp (0.00251953125:ℝ))^(256:ℕ) := by
        have h : (0.645:ℝ) = ((256:ℕ):ℝ) * 0.00251953125 := by norm_num
        rw [h, Real.exp_nat_mul]
      have hub : Real.exp (0.00251953125:ℝ) ≤ (1 - 0.00251953125)⁻¹ :=
        exp_upper _ (by norm_num) (by norm_num)
      have h3 : (Real.exp (0.00251953125:ℝ))^(256:ℕ)
          ≤ ((1 - 0.00251953125)⁻¹)^(256:ℕ) :=
        pow_le_pow_left₀ (Real.exp_pos _).le hub 256
      calc Real.exp (0.645:ℝ) = (Real.exp (0.00251953125:ℝ))^(256:ℕ) := h2
        _ ≤ ((1 - 0.00251953125)⁻¹)^(256:ℕ) := h3
        _ ≤ 1.908 := by norm_num
    calc (0.645:ℝ) = Real.log (Real.exp 0.645) := (Real.log_exp _).symm
      _ ≤ Real.log 1.908 := Real.log_le_log (Real.exp_pos _) hexp
  -- (c) log 227.712 ≤ 5.44
  have hlog227 : Real.log 227.712 ≤ (5.44:ℝ) := by
    have hexp : (227.712:ℝ) ≤ Real.exp (5.44:ℝ) := by
      have h1 : (0.006875:ℝ) + 1 ≤ Real.exp (0.006875:ℝ) := Real.add_one_le_exp _
      have h2 : Real.exp (0.44:ℝ) = (Real.exp (0.006875:ℝ))^(64:ℕ) := by
        have h : (0.44:ℝ) = ((64:ℕ):ℝ) * 0.006875 := by norm_num
        rw [h, Real.exp_nat_mul]
      have h3 : ((0.006875:ℝ) + 1)^(64:ℕ) ≤ (Real.exp (0.006875:ℝ))^(64:ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1 64
      have hexp044 : ((0.006875:ℝ) + 1)^(64:ℕ) ≤ Real.exp (0.44:ℝ) := by rw [h2]; exact h3
      have hexp5 : (2.7182818283:ℝ)^(5:ℕ) ≤ Real.exp (5:ℝ) := by
        rw [e5]; exact pow_le_pow_left₀ (by norm_num) egt.le 5
      calc (227.712:ℝ) ≤ (2.7182818283:ℝ)^(5:ℕ) * ((0.006875:ℝ) + 1)^(64:ℕ) := by norm_num
        _ ≤ Real.exp 5 * Real.exp 0.44 :=
            mul_le_mul hexp5 hexp044 (by positivity) (Real.exp_pos _).le
        _ = Real.exp (5.44:ℝ) := by rw [show (5.44:ℝ) = 5 + 0.44 by norm_num, Real.exp_add]
    calc Real.log 227.712 ≤ Real.log (Real.exp 5.44) := Real.log_le_log (by norm_num) hexp
      _ = 5.44 := Real.log_exp _
  -- (d) log 1.976 ≤ 0.69
  have hlog1976 : Real.log 1.976 ≤ (0.69:ℝ) := by
    have hexp : (1.976:ℝ) ≤ Real.exp (0.69:ℝ) := by
      have h1 : (0.01078125:ℝ) + 1 ≤ Real.exp (0.01078125:ℝ) := Real.add_one_le_exp _
      have h2 : Real.exp (0.69:ℝ) = (Real.exp (0.01078125:ℝ))^(64:ℕ) := by
        have h : (0.69:ℝ) = ((64:ℕ):ℝ) * 0.01078125 := by norm_num
        rw [h, Real.exp_nat_mul]
      have h3 : ((0.01078125:ℝ) + 1)^(64:ℕ) ≤ (Real.exp (0.01078125:ℝ))^(64:ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1 64
      calc (1.976:ℝ) ≤ ((0.01078125:ℝ) + 1)^(64:ℕ) := by norm_num
        _ ≤ (Real.exp (0.01078125:ℝ))^(64:ℕ) := h3
        _ = Real.exp (0.69:ℝ) := h2.symm
    calc Real.log 1.976 ≤ Real.log (Real.exp 0.69) := Real.log_le_log (by norm_num) hexp
      _ = 0.69 := Real.log_exp _
  -- (e) log 97000 ≤ 11.49
  have hlog97hi : Real.log 97000 ≤ (11.49:ℝ) := by
    have hexp : (97000:ℝ) ≤ Real.exp (11.49:ℝ) := by
      have h1 : (0.00765625:ℝ) + 1 ≤ Real.exp (0.00765625:ℝ) := Real.add_one_le_exp _
      have h2 : Real.exp (0.49:ℝ) = (Real.exp (0.00765625:ℝ))^(64:ℕ) := by
        have h : (0.49:ℝ) = ((64:ℕ):ℝ) * 0.00765625 := by norm_num
        rw [h, Real.exp_nat_mul]
      have h3 : ((0.00765625:ℝ) + 1)^(64:ℕ) ≤ (Real.exp (0.00765625:ℝ))^(64:ℕ) :=
        pow_le_pow_left₀ (by norm_num) h1 64
      have hexp049 : ((0.00765625:ℝ) + 1)^(64:ℕ) ≤ Real.exp (0.49:ℝ) := by rw [h2]; exact h3
      have hexp11 : (2.7182818283:ℝ)^(11:ℕ) ≤ Real.exp (11:ℝ) := by
        rw [e11]; exact pow_le_pow_left₀ (by norm_num) egt.le 11
      calc (97000:ℝ) ≤ (2.7182818283:ℝ)^(11:ℕ) * ((0.00765625:ℝ) + 1)^(64:ℕ) := by norm_num
        _ ≤ Real.exp 11 * Real.exp 0.49 :=
            mul_le_mul hexp11 hexp049 (by positivity) (Real.exp_pos _).le
        _ = Real.exp (11.49:ℝ) := by rw [show (11.49:ℝ) = 11 + 0.49 by norm_num, Real.exp_add]
    calc Real.log 97000 ≤ Real.log (Real.exp 11.49) := Real.log_le_log (by norm_num) hexp
      _ = 11.49 := Real.log_exp _
  -- (f) 11.405 ≤ log 97000
  have hlog97lo : (11.405:ℝ) ≤ Real.log 97000 := by
    have hexp : Real.exp (11.405:ℝ) ≤ (97000:ℝ) := by
      have h2 : Real.exp (0.405:ℝ) = (Real.exp (0.006328125:ℝ))^(64:ℕ) := by
        have h : (0.405:ℝ) = ((64:ℕ):ℝ) * 0.006328125 := by norm_num
        rw [h, Real.exp_nat_mul]
      have hub : Real.exp (0.006328125:ℝ) ≤ (1 - 0.006328125)⁻¹ :=
        exp_upper _ (by norm_num) (by norm_num)
      have hexp0405 : Real.exp (0.405:ℝ) ≤ ((1 - 0.006328125)⁻¹)^(64:ℕ) := by
        rw [h2]; exact pow_le_pow_left₀ (Real.exp_pos _).le hub 64
      have hexp11 : Real.exp (11:ℝ) ≤ (2.7182818286:ℝ)^(11:ℕ) := by
        rw [e11]; exact pow_le_pow_left₀ (Real.exp_pos _).le elt.le 11
      have hfin : (2.7182818286:ℝ)^(11:ℕ) * (((1 - 0.006328125)⁻¹)^(64:ℕ)) ≤ 97000 := by
        norm_num
      calc Real.exp (11.405:ℝ) = Real.exp 11 * Real.exp 0.405 := by
            rw [show (11.405:ℝ) = 11 + 0.405 by norm_num, Real.exp_add]
        _ ≤ (2.7182818286:ℝ)^(11:ℕ) * (((1 - 0.006328125)⁻¹)^(64:ℕ)) :=
            mul_le_mul hexp11 hexp0405 (by positivity) (by positivity)
        _ ≤ 97000 := hfin
    calc (11.405:ℝ) = Real.log (Real.exp 11.405) := (Real.log_exp _).symm
      _ ≤ Real.log 97000 := Real.log_le_log (Real.exp_pos _) hexp
  -- the deviation u = log b - log 97000 ≥ 0
  set u : ℝ := Real.log (b:ℝ) - Real.log 97000 with hu
  have hu0 : (0:ℝ) ≤ u := by
    have h7 : Real.log 97000 ≤ Real.log (b:ℝ) := Real.log_le_log (by norm_num) hbR
    rw [hu]; linarith
  have htu : Real.log (b:ℝ) = Real.log 97000 + u := by rw [hu]; ring
  have hb_eq : (b:ℝ) = 97000 * Real.exp u := by
    have h1 : Real.exp (Real.log (b:ℝ)) = (b:ℝ) := Real.exp_log hbpos
    have h2 : Real.exp (Real.log 97000) = (97000:ℝ) := Real.exp_log (by norm_num)
    rw [htu, Real.exp_add, h2] at h1
    exact h1.symm
  have hexpu : (1:ℝ) + u + u^2/4 ≤ Real.exp u := by
    have h1 : (u/2) + 1 ≤ Real.exp (u/2) := Real.add_one_le_exp _
    have h2 : ((u/2) + 1)^2 ≤ (Real.exp (u/2))^2 :=
      pow_le_pow_left₀ (by linarith [hu0]) h1 2
    have h3 : Real.exp u = (Real.exp (u/2))^2 := by
      rw [show u = u/2 + u/2 by ring, Real.exp_add]; ring
    have h4 : ((u/2) + 1)^2 = 1 + u + u^2/4 := by ring
    rw [h3, ← h4]; exact h2
  have hb_low : (97000:ℝ)*(1+u+u^2/4) ≤ (b:ℝ) := by
    rw [hb_eq]
    have hnn : (0:ℝ) ≤ 1+u+u^2/4 := by
      have hsq := sq_nonneg u; linarith [hu0]
    exact mul_le_mul (le_refl 97000) hexpu hnn (by norm_num)
  -- combined log bounds at b
  have hlog1908b : (0.645:ℝ) + Real.log (b:ℝ) ≤ Real.log (1.908*(b:ℝ)) := by
    have heq : Real.log (1.908*(b:ℝ)) = Real.log 1.908 + Real.log (b:ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hbpos)
    linarith [hlog1908]
  have hlog227b : Real.log (227.712*(b:ℝ)) ≤ (5.44:ℝ) + Real.log (b:ℝ) := by
    have heq : Real.log (227.712*(b:ℝ)) = Real.log 227.712 + Real.log (b:ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hbpos)
    linarith [hlog227]
  have hlog1976b : Real.log (1.976*(b:ℝ)) ≤ (0.69:ℝ) + Real.log (b:ℝ) := by
    have heq : Real.log (1.976*(b:ℝ)) = Real.log 1.976 + Real.log (b:ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hbpos)
    linarith [hlog1976]
  -- nonnegativity of the logs
  have hnn1908 : (0:ℝ) ≤ Real.log (1.908*(b:ℝ)) := by
    apply Real.log_nonneg
    calc (1:ℝ) = 1 * 1 := by norm_num
      _ ≤ 1.908 * (b:ℝ) := mul_le_mul (by norm_num) h1ble (by norm_num) (by norm_num)
  have hnn227 : (0:ℝ) ≤ Real.log (227.712*(b:ℝ)) := by
    apply Real.log_nonneg
    calc (1:ℝ) = 1 * 1 := by norm_num
      _ ≤ 227.712 * (b:ℝ) := mul_le_mul (by norm_num) h1ble (by norm_num) (by norm_num)
  have hnn1976 : (0:ℝ) ≤ Real.log (1.976*(b:ℝ)) := by
    apply Real.log_nonneg
    calc (1:ℝ) = 1 * 1 := by norm_num
      _ ≤ 1.976 * (b:ℝ) := mul_le_mul (by norm_num) h1ble (by norm_num) (by norm_num)
  have hD1 : (0:ℝ) < Real.log (1.908*(b:ℝ)) := by
    have htpos : (0:ℝ) < Real.log (b:ℝ) := Real.log_pos h1b
    linarith [hlog1908b]
  have hD2 : (0:ℝ) < Real.log (1.007:ℝ) := by
    have h := Real.log_pos (show (1:ℝ) < 1.007 by norm_num)
    linarith [hlog1007]
  have hDpos : (0:ℝ) < Real.log (1.908*(b:ℝ)) * Real.log 1.007 := mul_pos hD1 hD2
  -- lower bound for the denominator product
  have hD : ((0.645:ℝ)+11.405+u)*(0.006975:ℝ) ≤ Real.log (1.908*(b:ℝ)) * Real.log 1.007 := by
    have h1 : (0.645:ℝ)+11.405+u ≤ Real.log (1.908*(b:ℝ)) := by
      have h5 : (11.405:ℝ) + u ≤ Real.log (b:ℝ) := by
        have h7 : Real.log 97000 ≤ Real.log (b:ℝ) := Real.log_le_log (by norm_num) hbR
        linarith [hlog97lo, htu]
      linarith [hlog1908b]
    exact mul_le_mul h1 hlog1007 (by norm_num) hnn1908
  -- the key polynomial inequality in u
  have key : 18 * (((5.44:ℝ)+11.49+u) * ((0.69:ℝ)+11.49+u))
      ≤ (0.4553*97000*0.006975) * ((1+u+u^2/4) * ((0.645:ℝ)+11.405+u)) := by
    have hc0 : (0:ℝ) ≤ (0.4553*97000*0.006975)*(0.645+11.405)
        - 18*(5.44+11.49)*(0.69+11.49) := by norm_num
    have hc1 : (0:ℝ) ≤ (0.4553*97000*0.006975)*(0.645+11.405+1)
        - 18*(2*11.49+5.44+0.69) := by norm_num
    have hc2 : (0:ℝ) ≤ (0.4553*97000*0.006975)*(1+(0.645+11.405)/4) - 18 := by norm_num
    have hc3 : (0:ℝ) ≤ (0.4553*97000*0.006975)/4 := by norm_num
    have hu2 : (0:ℝ) ≤ u^2 := pow_nonneg hu0 2
    have hu3 : (0:ℝ) ≤ u^3 := pow_nonneg hu0 3
    have hpos : (0:ℝ) ≤ ((0.4553*97000*0.006975)/4)*u^3
        + (((0.4553*97000*0.006975)*(1+(0.645+11.405)/4) - 18)*u^2
        + (((0.4553*97000*0.006975)*(0.645+11.405+1) - 18*(2*11.49+5.44+0.69))*u
        + ((0.4553*97000*0.006975)*(0.645+11.405) - 18*(5.44+11.49)*(0.69+11.49)))) :=
      add_nonneg (mul_nonneg hc3 hu3)
        (add_nonneg (mul_nonneg hc2 hu2) (add_nonneg (mul_nonneg hc1 hu0) hc0))
    have hexpand : (0.4553*97000*0.006975) * ((1+u+u^2/4) * ((0.645:ℝ)+11.405+u))
        - 18 * (((5.44:ℝ)+11.49+u) * ((0.69:ℝ)+11.49+u))
        = ((0.4553*97000*0.006975)/4)*u^3
        + (((0.4553*97000*0.006975)*(1+(0.645+11.405)/4) - 18)*u^2
        + (((0.4553*97000*0.006975)*(0.645+11.405+1) - 18*(2*11.49+5.44+0.69))*u
        + ((0.4553*97000*0.006975)*(0.645+11.405) - 18*(5.44+11.49)*(0.69+11.49)))) := by ring
    linarith
  -- upper bound for the numerator product
  have hN : Real.log (227.712*(b:ℝ)) * Real.log (1.976*(b:ℝ))
      ≤ ((5.44:ℝ)+11.49+u) * ((0.69:ℝ)+11.49+u) := by
    have g1 : Real.log (227.712*(b:ℝ)) ≤ (5.44:ℝ)+11.49+u := by
      have h5 : Real.log (b:ℝ) ≤ (11.49:ℝ) + u := by
        linarith [hlog97hi, htu]
      linarith [hlog227b]
    have g2 : Real.log (1.976*(b:ℝ)) ≤ (0.69:ℝ)+11.49+u := by
      have h5 : Real.log (b:ℝ) ≤ (11.49:ℝ) + u := by
        linarith [hlog97hi, htu]
      linarith [hlog1976b]
    have hA2 : (0:ℝ) ≤ (5.44:ℝ)+11.49+u := by linarith [hu0]
    exact mul_le_mul g1 g2 hnn1976 hA2
  -- main inequality: 18 * N ≤ 0.4553 * b * D
  have hmain : 18 * Real.log (227.712*(b:ℝ)) * Real.log (1.976*(b:ℝ))
      ≤ 0.4553 * (b:ℝ) * (Real.log (1.908*(b:ℝ)) * Real.log 1.007) := by
    have e1 : 18 * (Real.log (227.712*(b:ℝ)) * Real.log (1.976*(b:ℝ)))
        ≤ 18 * (((5.44:ℝ)+11.49+u) * ((0.69:ℝ)+11.49+u)) :=
      mul_le_mul (le_refl 18) hN (mul_nonneg hnn227 hnn1976) (by norm_num)
    have e2 : (0.4553*97000*0.006975) * ((1+u+u^2/4) * ((0.645:ℝ)+11.405+u))
        ≤ 0.4553 * ((b:ℝ) * (Real.log (1.908*(b:ℝ)) * Real.log 1.007)) := by
      have h_a : (0.4553:ℝ) * ((97000:ℝ)*(1+u+u^2/4)) ≤ 0.4553 * (b:ℝ) :=
        mul_le_mul (le_refl 0.4553) hb_low
          (mul_nonneg (by norm_num) (by have hsq := sq_nonneg u; linarith [hu0]))
          (by norm_num)
      have g3 : (0.4553:ℝ) * ((97000:ℝ)*(1+u+u^2/4)) * (((0.645:ℝ)+11.405+u)*(0.006975:ℝ))
          ≤ (0.4553 * (b:ℝ)) * (Real.log (1.908*(b:ℝ)) * Real.log 1.007) :=
        mul_le_mul h_a hD
          (mul_nonneg (by linarith [hu0]) (by norm_num))
          (mul_nonneg (by norm_num) hbpos.le)
      have geq : (0.4553*97000*0.006975) * ((1+u+u^2/4) * ((0.645:ℝ)+11.405+u))
          = (0.4553:ℝ) * ((97000:ℝ)*(1+u+u^2/4)) * (((0.645:ℝ)+11.405+u)*(0.006975:ℝ)) := by ring
      linarith
    linarith [e1, key, e2]
  -- combine hlo and hhi against hmain
  have hlt : (0.4553:ℝ)*(b:ℝ)*(Real.log (1.908*(b:ℝ)) * Real.log 1.007)
      < 18 * Real.log (227.712*(b:ℝ)) * Real.log (1.976*(b:ℝ)) := by
    rw [lt_div_iff₀ hDpos] at hhi
    have h2 : (n:ℝ) * (Real.log (1.908*(b:ℝ)) * Real.log 1.007)
        < 18 * Real.log (227.712*(b:ℝ)) * Real.log (1.976*(b:ℝ)) := hhi
    calc (0.4553:ℝ)*(b:ℝ)*(Real.log (1.908*(b:ℝ)) * Real.log 1.007)
        < (n:ℝ)*(Real.log (1.908*(b:ℝ)) * Real.log 1.007) :=
          mul_lt_mul_of_pos_right hlo hDpos
      _ < 18 * Real.log (227.712*(b:ℝ)) * Real.log (1.976*(b:ℝ)) := h2
  linarith [hlt, hmain]
