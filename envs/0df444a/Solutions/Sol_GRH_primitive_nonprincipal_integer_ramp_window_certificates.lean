-- Prove2me | solution 1 for GRH.primitive_nonprincipal_integer_ramp_window_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T17:05:18.270141+00:00
-- url     : https://prove2.me/submissions/c2283047-1e74-40be-8142-8a364967e272
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_primitive_nonprincipal_fourth_power_ramp_window_certificates
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset ArithmeticFunction Set

noncomputable section

private def ramp (x : ℝ) (n : ℕ) : ℝ :=
  max (x - n) 0 / n

private theorem ramp_eq (x : ℝ) (n : ℕ) :
    ramp x n = max (x / (n : ℝ) - 1) 0 := by
  by_cases hn : n = 0
  · norm_num [ramp, hn]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold ramp
  rw [← max_div_div_right hnR.le, sub_div, div_self hnR.ne', zero_div]

private def correctedRamp (c : ℕ → ℝ) (d : ℝ) (k : ℕ) : ℝ :=
  (∑ n ∈ range (k+1), c n * ramp k n) + k * d

private theorem correctedRamp_extend (c : ℕ → ℝ) (d : ℝ) {k b : ℕ} (hkb : k ≤ b) :
    correctedRamp c d k = (∑ n ∈ range (b+1), c n * ramp k n) + k * d := by
  unfold correctedRamp
  congr 1
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n _ hn
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (show k ≤ n by
    simp only [Finset.mem_range, not_lt] at hn
    omega)
  simp [ramp, max_eq_right (sub_nonpos.mpr hkn)]

/-- The deviation from the chord only receives contributions from knots in `(a,b]`. -/
private theorem ramp_chord (c : ℕ → ℝ) (d : ℝ) {a k b : ℕ}
    (ha : 0 < a) (hak : a ≤ k) (hkb : k ≤ b) (hab : a < b) {A : ℝ}
    (hA : 0 ≤ A) (hc : ∀ n ∈ Finset.Ioc a b, |c n| ≤ A) :
    let t := ((k : ℝ) - a) / ((b : ℝ) - a)
    correctedRamp c d k ≤ (1-t) * correctedRamp c d a + t * correctedRamp c d b +
      (((b : ℝ) - a)^2 / a) * A := by
  dsimp only
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hakR : (a : ℝ) ≤ k := by exact_mod_cast hak
  have hkbR : (k : ℝ) ≤ b := by exact_mod_cast hkb
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hgap : 0 < (b : ℝ) - a := sub_pos.mpr habR
  let t := ((k : ℝ) - a) / ((b : ℝ) - a)
  change correctedRamp c d k ≤ (1-t) * correctedRamp c d a + t * correctedRamp c d b + _
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hakR) hgap.le
  have ht1 : t ≤ 1 := (div_le_one hgap).mpr (sub_le_sub_right hkbR _)
  have hk : (k : ℝ) = (1-t) * a + t * b := by
    have htgap : t * ((b : ℝ) - a) = (k : ℝ) - a := div_mul_cancel₀ _ hgap.ne'
    linarith
  let err (n : ℕ) := c n * (ramp k n - (1-t) * ramp a n - t * ramp b n)
  have hsum : (∑ n ∈ Finset.Ioc a b, err n) = ∑ n ∈ range (b+1), err n := by
    apply Finset.sum_subset
    · simp only [Finset.subset_iff, Finset.mem_Ioc, Finset.mem_range]
      omega
    intro n hn hnIoc
    have hnb : n ≤ b := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
    have hna : n ≤ a := by
      simp only [Finset.mem_Ioc] at hnIoc
      omega
    have hnaR : (n : ℝ) ≤ a := by exact_mod_cast hna
    simp only [err, ramp, max_eq_left (sub_nonneg.mpr hnaR),
      max_eq_left (sub_nonneg.mpr (hnaR.trans hakR)),
      max_eq_left (sub_nonneg.mpr (hnaR.trans habR.le))]
    rw [hk]
    simp only [div_eq_mul_inv]
    ring
  have hlocal (n : ℕ) (hn : n ∈ Finset.Ioc a b) :
      err n ≤ (((b : ℝ) - a) / a) * A := by
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.mp hn
    have hanR : (a : ℝ) ≤ n := by exact_mod_cast han.le
    have hnbR : (n : ℝ) ≤ b := by exact_mod_cast hnb
    have hnR : 0 < (n : ℝ) := haR.trans_le hanR
    have hra : ramp a n = 0 := by simp [ramp, max_eq_right (sub_nonpos.mpr hanR)]
    have hrk0 : 0 ≤ ramp k n := div_nonneg (le_max_right _ _) hnR.le
    have hrkb : ramp k n ≤ ramp b n := by
      unfold ramp
      gcongr
    have hrb : ramp b n ≤ ((b : ℝ) - a) / a := by
      rw [ramp, max_eq_left (sub_nonneg.mpr hnbR)]
      gcongr
    have htpart0 : 0 ≤ t * ramp b n := mul_nonneg ht0 (hrk0.trans hrkb)
    have htpart1 : t * ramp b n ≤ ramp b n := mul_le_of_le_one_left (hrk0.trans hrkb) ht1
    have habs : |ramp k n - t * ramp b n| ≤ ((b : ℝ) - a) / a :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    simp only [err, hra, mul_zero, sub_zero]
    calc
      _ ≤ |c n * (ramp k n - t * ramp b n)| := le_abs_self _
      _ ≤ A * (((b : ℝ) - a) / a) := by
        rw [abs_mul]
        exact mul_le_mul (hc n hn) habs (abs_nonneg _) hA
      _ = _ := mul_comm _ _
  have herror : (∑ n ∈ range (b+1), err n) ≤ (((b : ℝ) - a)^2 / a) * A := by
    rw [← hsum]
    calc
      _ ≤ ∑ _n ∈ Finset.Ioc a b, (((b : ℝ) - a) / a) * A := Finset.sum_le_sum hlocal
      _ = _ := by
        simp [Nat.card_Ioc, Nat.cast_sub hab.le]
        ring
  rw [correctedRamp_extend c d hkb, correctedRamp_extend c d hab.le,
    correctedRamp_extend c d (le_refl b)]
  have hd : (k : ℝ) * d = (1-t) * (a * d) + t * (b * d) := by
    calc
      (k : ℝ) * d = ((1-t) * a + t * b) * d := congrArg (· * d) hk
      _ = _ := by ring
  simp only [err, mul_sub, Finset.sum_sub_distrib, mul_left_comm (c _),
    ← Finset.mul_sum] at herror
  linarith only [herror, hd]

private theorem rpow_sixteen {u v η : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u)
    (huv : u ≤ 16 * v) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    u^η ≤ 16 * v^η := by
  calc
    u^η ≤ (16*v)^η := Real.rpow_le_rpow hu huv hη0
    _ = (16:ℝ)^η * v^η := Real.mul_rpow (by norm_num) hv
    _ ≤ 16*v^η := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hv _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16) hη1

private theorem fourth_power_chord {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℝ) {j k : ℕ} (hj : 1 ≤ j) (hjk : j^4 ≤ k) (hkj : k ≤ (j+1)^4)
    {θ C : ℝ} (hθ : 1/2 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) :
    let c := fun n : ℕ => vonMangoldt n * (χ (n:ZMod q)).re
    correctedRamp c d (j^4) ≤ C * ((j^4 : ℕ):ℝ)^θ →
    correctedRamp c d ((j+1)^4) ≤ C * (((j+1)^4 : ℕ):ℝ)^θ →
    correctedRamp c d k ≤ (16*C + 16384/(θ-1/2)) * (k:ℝ)^θ := by
  intro c hleft hright
  let a := j^4
  let b := (j+1)^4
  have ha : 0 < a := pow_pos (by omega) _
  have hab : a < b := by
    dsimp [a, b]
    gcongr
    omega
  have hjR : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hj0 : 0 ≤ (j : ℝ) := by positivity
  have haR : (a : ℝ) = (j : ℝ)^4 := by simp [a]
  have hbR : (b : ℝ) = ((j : ℝ)+1)^4 := by simp [b]
  have hgap : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab.le)
  have hgapMax : (b : ℝ) - a ≤ 32*(j : ℝ)^3 := by
    rw [haR, hbR]
    have h₁ : ((j : ℝ)+1)^4 - (j : ℝ)^4 ≤ 4*((j : ℝ)+1)^3 := by
      nlinarith [sq_nonneg (j : ℝ)]
    have h₂ : ((j : ℝ)+1)^3 ≤ (2*(j : ℝ))^3 := by
      gcongr
      linarith
    nlinarith
  have hb16 : (b : ℝ) ≤ 16*k := by
    have h₁ : ((j : ℝ)+1)^4 ≤ (2*(j : ℝ))^4 := by
      gcongr
      linarith
    have h₂ : (a : ℝ) ≤ k := by exact_mod_cast hjk
    rw [haR] at h₂
    rw [hbR]
    nlinarith
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkθ0 : 0 ≤ (k : ℝ)^θ := Real.rpow_nonneg hk0 _
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  let ε := θ - 1/2
  have hε : 0 < ε := sub_pos.mpr hθ
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith
  have hcoeff (n : ℕ) (hn : n ∈ Finset.Ioc a b) : |c n| ≤ 16*(k:ℝ)^ε/ε := by
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast ha.trans han
    have hn16 : (n : ℝ) ≤ 16*k := (Nat.cast_le.mpr hnb).trans hb16
    have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn0 ε)
    rw [Real.log_rpow hn0] at hlog
    have hχ : |(χ (n:ZMod q)).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
    calc
      |c n| ≤ vonMangoldt n := by
        dsimp only [c]
        rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg (n := n))]
        exact mul_le_of_le_one_right vonMangoldt_nonneg hχ
      _ ≤ Real.log n := vonMangoldt_le_log
      _ ≤ 16*(k:ℝ)^ε/ε := (le_div_iff₀ hε).mpr (by
        have hp := rpow_sixteen hk0 hn0.le hn16 hε.le hε1
        linarith)
  have hgapSq : ((b : ℝ) - a)^2 / a ≤ 1024*(k:ℝ)^(1/2:ℝ) := by
    have hsq : ((b : ℝ)-a)^2 ≤ (32*(j:ℝ)^3)^2 := by gcongr
    have hroot : (j:ℝ)^2 ≤ (k:ℝ)^(1/2:ℝ) := by
      have hpow := Real.rpow_le_rpow ha0.le (Nat.cast_le.mpr hjk) (by norm_num : (0:ℝ) ≤ 1/2)
      rw [haR, ← Real.rpow_natCast, ← Real.rpow_mul hj0] at hpow
      norm_num at hpow
      simpa only [Real.rpow_natCast] using hpow
    apply (div_le_iff₀ ha0).mpr
    calc
      _ ≤ (32*(j:ℝ)^3)^2 := hsq
      _ = (1024*(j:ℝ)^2)*(a:ℝ) := by rw [haR]; ring
      _ ≤ _ := by gcongr
  have hka : 0 < (k : ℝ) := ha0.trans_le (Nat.cast_le.mpr hjk)
  have herr :
      (((b : ℝ) - a)^2 / a) * (16*(k:ℝ)^ε/ε) ≤ (16384/ε) * (k:ℝ)^θ := by
    calc
      _ ≤ (1024*(k:ℝ)^(1/2:ℝ))*(16*(k:ℝ)^ε/ε) := by gcongr
      _ = (16384/ε) * ((k:ℝ)^(1/2:ℝ) * (k:ℝ)^ε) := by ring
      _ = _ := by rw [← Real.rpow_add hka, show 1/2 + ε = θ by dsimp [ε]; ring]
  have hright' : correctedRamp c d b ≤ (16*C) * (k:ℝ)^θ := by
    calc
      _ ≤ C * (b:ℝ)^θ := hright
      _ ≤ C * (16*(k:ℝ)^θ) := mul_le_mul_of_nonneg_left
        (rpow_sixteen hk0 (by positivity) hb16 (by linarith) hθ1) hC
      _ = _ := by ring
  have hleft' : correctedRamp c d a ≤ (16*C) * (k:ℝ)^θ := by
    calc
      _ ≤ C * (a:ℝ)^θ := hleft
      _ ≤ C * (k:ℝ)^θ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ha0.le (Nat.cast_le.mpr hjk) (by linarith)) hC
      _ ≤ _ := by
        gcongr
        linarith
  have hchord := ramp_chord c d ha hjk hkj hab (by positivity) hcoeff
  let t := ((k : ℝ) - a) / ((b : ℝ) - a)
  have ht0 : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hjk)) hgap
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr (Nat.cast_lt.mpr hab))).mpr
    (sub_le_sub_right (Nat.cast_le.mpr hkj) _)
  change correctedRamp c d k ≤ (1-t)*correctedRamp c d a + t*correctedRamp c d b + _ at hchord
  calc
    _ ≤ (1-t)*correctedRamp c d a + t*correctedRamp c d b +
        (((b : ℝ) - a)^2 / a) * (16*(k:ℝ)^ε/ε) := hchord
    _ ≤ (1-t)*((16*C)*(k:ℝ)^θ) + t*((16*C)*(k:ℝ)^θ) +
        (16384/ε)*(k:ℝ)^θ := by gcongr
    _ = _ := by ring

theorem solution :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ M₀ : ℕ, ∃ M : ℕ, M₀ ≤ M ∧ 1 ≤ M ∧
          ∀ k ∈ Finset.Icc M (⌊(M:ℝ)^(1+δ)⌋₊+1),
          (∑ n ∈ range (k+1), vonMangoldt n * (χ (n:ZMod q)).re *
            max ((k:ℝ)/(n:ℝ)-1) 0) +
            (k:ℝ) * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*(k:ℝ)^θ := by
  classical
  intro q _ χ hprim hnon θ hθ hθmax
  obtain ⟨δ, C, hδ, hC, hband⟩ :=
    GRH.primitive_nonprincipal_fourth_power_ramp_window_certificates q χ hprim hnon θ hθ hθmax
  have hθ1 : θ ≤ 1 := hθmax.trans (by norm_num)
  have hε : 0 < θ - 1/2 := sub_pos.mpr hθ
  refine ⟨δ, 16*C + 16384/(θ-1/2), hδ, by positivity, ?_⟩
  intro M₀
  obtain ⟨K, hKM, hK, hcert⟩ := hband M₀
  have hKK : K ≤ K^4 := by simpa using Nat.pow_le_pow_right hK (by norm_num : 1 ≤ 4)
  refine ⟨K^4, hKM.trans hKK, hK.trans hKK, ?_⟩
  intro k hk
  obtain ⟨hKk, hku⟩ := Finset.mem_Icc.mp hk
  have hex : ∃ m : ℕ, k < m^4 := ⟨k+1, by
    have hm : k+1 ≤ (k+1)^4 := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ k+1) (by norm_num : 1 ≤ 4)
    omega⟩
  let j := Nat.find hex - 1
  have hfind0 : Nat.find hex ≠ 0 := by
    intro hz
    have hh := Nat.find_spec hex
    simp [hz] at hh
  have hjfind : j+1 = Nat.find hex := by dsimp [j]; omega
  have hkj : k < (j+1)^4 := by
    rw [hjfind]
    exact Nat.find_spec hex
  have hjk : j^4 ≤ k := by
    by_contra! hh
    have hmin := Nat.find_min' hex hh
    omega
  have hjK : K ≤ j := by
    by_contra! hh
    have hhpow : (j+1)^4 ≤ K^4 := by
      gcongr
      omega
    omega
  have hleft := hcert j hjK ((Nat.pow_le_pow_left (Nat.sub_le j 1) _).trans
    (hjk.trans hku))
  have hright := hcert (j+1) (by omega) (by simpa using hjk.trans hku)
  simpa only [correctedRamp, ramp_eq] using
    fourth_power_chord χ (deriv χ.LFunction 1 / χ.LFunction 1).re
      (hK.trans hjK) hjk hkj.le hθ hθ1 hC
      (by simpa only [correctedRamp, ramp_eq] using hleft)
      (by simpa only [correctedRamp, ramp_eq] using hright)
