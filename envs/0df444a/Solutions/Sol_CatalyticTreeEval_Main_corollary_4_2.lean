-- Prove2me | solution 1 for CatalyticTreeEval.Main.corollary_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:04:12.669402+00:00
-- url     : https://prove2.me/submissions/3e390679-b236-415c-a107-9f3705336d88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CatalyticTreeEval_Main_theorem_4_1
import Theorems.Thm_CatalyticTreeEval_Main_bit_tape_simulation

set_option autoImplicit false

open CatalyticTreeEval.Main

/-- Theorem 4.1 converted to arbitrary bit tapes by the shifted-block simulation. -/
theorem solution (F : List Bool → Frame) (domain : Set (List Bool))
    (MV MD : Machine) (A : ℕ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (F a).valid ∧ a.length ≤ 2 ^ (A * (F a).s) ∧ (F a).access a MV MD A) :
    ∃ (M : Machine) (Cs Cc Ct B : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < B ∧ 0 < q ∧
      ∀ a ∈ domain, ∀ h : ℕ, 0 < h → ∀ I : Tree (F a).l h,
      ComputesPrefix M (listCode ((F a).params a) ++ I.encode) (bits (F a).l I.value.val)
        (Cs * ((F a).l + h * (lg (F a).k + log₂ (F a).m) + (F a).s))
        (Cc * (F a).d * (1 + log₂ ((F a).d * (F a).m)))
        (Ct * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q) := by
  obtain ⟨M, Cs₀, Ct₀, B₀, q₀, hCs₀, hCt₀, hB₀, hq₀, hreg⟩ :=
    theorem_4_1 F domain MV MD A hA h
  obtain ⟨simulate, Cs, Cc, Ct, q, hCs, hCc, hCt, hq, hsim⟩ :=
    bit_tape_simulation
  refine ⟨simulate M, Cs * (Cs₀ + 1), Cc, Ct * (Ct₀ + 1), B₀ + 1,
    q₀ + 2 * q, by positivity, hCc, by positivity, by positivity, by omega, ?_⟩
  intro a ha n hn I
  have hF := (h a ha).1
  rcases hF with ⟨hm, hl, hmatch, hnoncancel, hdec, hs⟩
  have hk : 0 < (F a).k := by
    by_contra hk
    have hk0 : (F a).k = 0 := Nat.eq_zero_of_not_pos hk
    have hone : (1 : ZMod (F a).m) ≠ 0 := by
      intro heq
      have hv := congrArg ZMod.val heq
      rw [ZMod.val_one_eq_one_mod, ZMod.val_zero, Nat.mod_eq_of_lt hm] at hv
      omega
    apply hone
    have hs := hdec.2.2
    have he : (Finset.univ : Finset (Fin (F a).k)) = ∅ := by
      ext j
      have hlt := j.isLt
      simp [hk0] at hlt
    rw [he] at hs
    simpa using hs.symm
  have hlogm : 0 ≤ log₂ (F a).m := by
    unfold log₂
    have hmreal : (1 : ℝ) ≤ (F a).m := by exact_mod_cast (show 1 ≤ (F a).m by omega)
    exact div_nonneg (Real.log_nonneg hmreal) (by positivity)
  have hlgk : 0 ≤ lg (F a).k := by
    unfold lg log₂
    have hk0 : (0 : ℝ) ≤ (F a).k := by positivity
    have hkreal : (1 : ℝ) ≤ (F a).k + 1 := by linarith
    have hlog : 0 ≤ Real.log ((F a).k + 1 : ℝ) := Real.log_nonneg hkreal
    positivity
  have hbase : (F a).s + 1 ≤
      (F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s := by
    have hterm : 0 ≤ (n : ℝ) * (lg (F a).k + log₂ (F a).m) :=
      mul_nonneg (by positivity) (add_nonneg hlgk hlogm)
    have hl1 : (1 : ℝ) ≤ (F a).l := by exact_mod_cast hl
    linarith
  let S : ℝ := Cs₀ * ((F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s)
  let T : ℝ := Ct₀ * (B₀ * (F a).k) ^ n *
    ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q₀
  let X : ℝ := (2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s
  let Y₀ : ℝ := (B₀ * (F a).k) ^ n
  let Y₁ : ℝ := ((B₀ + 1) * (F a).k) ^ n
  have hS : 0 ≤ S := by
    dsimp [S]
    have hl0 : (0 : ℝ) ≤ (F a).l := by positivity
    have hs0 : (0 : ℝ) ≤ (F a).s := by positivity
    have hterm : 0 ≤ (n : ℝ) * (lg (F a).k + log₂ (F a).m) :=
      mul_nonneg (by positivity) (add_nonneg hlgk hlogm)
    positivity
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hrun := hsim (F a) ⟨hm, hl, hmatch, hnoncancel, hdec, hs⟩ M
    (listCode ((F a).params a) ++ I.encode) (bits (F a).l I.value.val) S T hS hT
    (fun R => hreg a ha n hn I R)
  have hspace : Cs * (S + (F a).s + 1) ≤
      Cs * (Cs₀ + 1) * ((F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s) := by
    have hb := mul_le_mul_of_nonneg_left hbase (le_of_lt hCs)
    dsimp [S]
    calc
      Cs * (Cs₀ * ((F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s) +
          (F a).s + 1) ≤
        Cs * (Cs₀ * ((F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s) +
          ((F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s)) := by
            nlinarith
      _ = Cs * (Cs₀ + 1) *
          ((F a).l + n * (lg (F a).k + log₂ (F a).m) + (F a).s) := by ring
  have hXtwo : (2 : ℝ) ≤ X := by
    have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (F a).l := by
      have hl1 : 1 ≤ (F a).l := hl
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ (F a).l := by gcongr <;> norm_num
    have hk0 : (0 : ℝ) ≤ (F a).k := by positivity
    have hd0 : (0 : ℝ) ≤ (F a).d := by positivity
    have hs0 : (0 : ℝ) ≤ (2 : ℝ) ^ (F a).s := by positivity
    dsimp [X]
    linarith
  have hXs : (2 : ℝ) ^ (F a).s ≤ X := by
    have hl0 : (0 : ℝ) ≤ (2 : ℝ) ^ (F a).l := by positivity
    have hk0 : (0 : ℝ) ≤ (F a).k := by positivity
    have hd0 : (0 : ℝ) ≤ (F a).d := by positivity
    dsimp [X]
    linarith
  have hY : Y₀ ≤ Y₁ := by
    dsimp [Y₀, Y₁]
    apply pow_le_pow_left₀ (by positivity)
    have hkreal : (0 : ℝ) ≤ (F a).k := by positivity
    nlinarith
  have hYone : 1 ≤ Y₁ := by
    dsimp [Y₁]
    apply one_le_pow₀
    have hkreal : (1 : ℝ) ≤ (F a).k := by exact_mod_cast hk
    nlinarith
  have hXq₀ : 1 ≤ X ^ q₀ := one_le_pow₀ (by linarith)
  have hXtwoq : 1 ≤ X ^ (2 * q) := one_le_pow₀ (by linarith)
  have hover : ((2 : ℝ) ^ (F a).s + 1) ^ q ≤ X ^ (2 * q) := by
    calc
      ((2 : ℝ) ^ (F a).s + 1) ^ q ≤ ((2 : ℝ) * (2 : ℝ) ^ (F a).s) ^ q := by
        apply pow_le_pow_left₀ (by positivity)
        have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (F a).s := one_le_pow₀ (by norm_num)
        linarith
      _ ≤ (X ^ 2) ^ q := by
        apply pow_le_pow_left₀ (by positivity)
        have hXnonneg : 0 ≤ X := by linarith
        have hsnonneg : 0 ≤ (2 : ℝ) ^ (F a).s := by positivity
        nlinarith [sq_nonneg (X - 2), sq_nonneg (X - (2 : ℝ) ^ (F a).s)]
      _ = X ^ (2 * q) := by rw [← pow_mul]
  have htime : Ct * (T + ((2 : ℝ) ^ (F a).s + 1) ^ q) ≤
      Ct * (Ct₀ + 1) * (Y₁ * X ^ (q₀ + 2 * q)) := by
    have hfirst : Ct * T ≤ Ct * Ct₀ * (Y₁ * X ^ (q₀ + 2 * q)) := by
      dsimp [T, Y₀]
      calc
        Ct * (Ct₀ * (B₀ * (F a).k) ^ n * X ^ q₀) =
            Ct * Ct₀ * Y₀ * X ^ q₀ * 1 := by dsimp [Y₀]; ring
        _ ≤ Ct * Ct₀ * Y₁ * X ^ q₀ * X ^ (2 * q) := by gcongr
        _ = Ct * Ct₀ * (Y₁ * X ^ (q₀ + 2 * q)) := by rw [pow_add]; ring
    have hsecond : Ct * ((2 : ℝ) ^ (F a).s + 1) ^ q ≤
        Ct * (Y₁ * X ^ (q₀ + 2 * q)) := by
      calc
        Ct * ((2 : ℝ) ^ (F a).s + 1) ^ q ≤ Ct * X ^ (2 * q) := by gcongr
        _ = Ct * (1 * 1 * X ^ (2 * q)) := by ring
        _ ≤ Ct * (Y₁ * X ^ q₀ * X ^ (2 * q)) := by gcongr
        _ = Ct * (Y₁ * X ^ (q₀ + 2 * q)) := by rw [pow_add]; ring
    rw [mul_add]
    calc
      Ct * T + Ct * ((2 : ℝ) ^ (F a).s + 1) ^ q ≤
          Ct * Ct₀ * (Y₁ * X ^ (q₀ + 2 * q)) + Ct * (Y₁ * X ^ (q₀ + 2 * q)) :=
        add_le_add hfirst hsecond
      _ = Ct * (Ct₀ + 1) * (Y₁ * X ^ (q₀ + 2 * q)) := by ring
  intro τ hτ
  obtain ⟨t, c, hcrun, hcstate, hcoutput, hcrest, hcwork, hctime, hchead⟩ := hrun τ hτ
  refine ⟨t, c, hcrun, hcstate, hcoutput, hcrest, ?_, ?_, hchead⟩
  · intro u hu cu hcu
    exact lt_of_lt_of_le (hcwork u hu cu hcu) (Nat.ceil_mono hspace)
  · calc
      (t : ℝ) ≤ Ct * (T + ((2 : ℝ) ^ (F a).s + 1) ^ q) := hctime
      _ ≤ Ct * (Ct₀ + 1) * (Y₁ * X ^ (q₀ + 2 * q)) := htime
      _ = (Ct * (Ct₀ + 1) * ((B₀ + 1) * (F a).k) ^ n) * X ^ (q₀ + 2 * q) := by
        dsimp [Y₁]
        ring
