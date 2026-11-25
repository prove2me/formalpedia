-- Prove2me | solution 1 for DetDLP.lemma_3_2_collision_potential
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:17:28.212417+00:00
-- url     : https://prove2.me/submissions/7c79efa1-5a2f-4ec1-b25f-69dc5359dbd5

import Mathlib
import Definitions.Def_DetDLP_FactorBase

import Theorems.Thm_DetDLP_collision_energy_moment_bound
import Theorems.Thm_DetDLP_collision_variance_moment_bound

set_option autoImplicit false

open DetDLP

private theorem collision_budget (m : ℕ) (hm : 2 ≤ m) {q : ℝ} (hq : 4096 * (m : ℝ) ≤ q) :
    1 / 16 + (8193 / 8192 : ℝ) * ((1 + 2/q)^m + 4 * (2/q)^m) +
        64 * ((1 + 2/q)^m - 1) ≤ 373 / 336 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq' : 8192 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  let x := 2 / q
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 1/4096 := (div_le_iff₀ hq0).mpr (by linarith)
  have hmx : (m : ℝ) * x ≤ 1/2048 := by
    dsimp [x]; rw [← mul_div_assoc]
    apply (div_le_iff₀ hq0).mpr
    linarith
  have hbern := one_add_mul_le_pow (a := -x) (by linarith : -2 ≤ -x) m
  have hgeom : (1 + x)^m ≤ 2048/2047 := by
    have hprod : (1+x)^m * (1-x)^m ≤ 1 := by
      rw [← mul_pow]
      apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg x])
    have hden : 2047 / 2048 ≤ (1-x)^m := by
      rw [sub_eq_add_neg]
      nlinarith [hbern]
    nlinarith [mul_le_mul_of_nonneg_left hden (pow_nonneg (show 0 ≤ 1 + x by linarith) m)]
  have hxpow : x^m ≤ (1 / 4096 : ℝ)^2 := by
    exact (pow_le_pow_of_le_one hx0 (by linarith) hm).trans (pow_le_pow_left₀ hx0 hx _)
  change 1/16 + _ * ((1+x)^m + 4*x^m) + _ * ((1+x)^m-1) ≤ _
  linarith

private theorem collision_parameter_power {m : ℕ} (hm : 2 ≤ m) {g q : ℝ}
    (hg : 0 ≤ g) (hq : (16*g) ^ ((1:ℝ)/(m:ℝ)) ≤ q) : 16*g ≤ q^m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hg' : 0 ≤ 16*g := by positivity
  calc
    16*g = ((16*g) ^ ((1:ℝ)/(m:ℝ))) ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hg', div_mul_cancel₀ _ hm', Real.rpow_one]
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hg' _) hq _

private theorem parameter_lower_bounds (p n m g : ℕ) (hp : 0 < p) (hn : 0 < n) (hm : 2 ≤ m) :
    let q := qBlk p n (hashThreshold p n m g)
    4096 * (m : ℝ) ≤ q ∧ 16 * (g : ℝ) ≤ q ^ m := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hb : (qStar m g : ℝ) ≤ qBlk p n (hashThreshold p n m g) := by
    unfold qBlk hashThreshold
    apply (le_div_iff₀ hp').mpr
    have ht := (div_le_iff₀ hn').mp (Nat.le_ceil (((p : ℝ) * qStar m g) / (n : ℝ)))
    linarith
  constructor
  · apply le_trans _ hb
    exact_mod_cast (show 4096*m ≤ qStar m g from le_max_left _ _)
  · apply collision_parameter_power hm (Nat.cast_nonneg g)
    apply le_trans _ hb
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show Nat.ceil ((16 * (g : ℝ)) ^ ((1 : ℝ) / m)) ≤ qStar m g from le_max_right _ _)

private theorem combine_moments {ι : Type*} [Fintype ι] (m : ℕ) (hm : 2 ≤ m)
    (g n q μ : ℝ) (hg : 0 ≤ g) (hn : 8192 ≤ n) (hgn : g ≤ n + 1)
    (hq : 4096 * (m : ℝ) ≤ q) (hμ : 0 < μ) (hdiag : 16*g ≤ μ)
    (energy deviation : ι → ℝ)
    (he : (∑ i, energy i) / (Fintype.card ι : ℝ) ≤
      μ + μ^2/n * ((1+2/q)^m + 4*(2/q)^m))
    (hv : (∑ i, deviation i) / (Fintype.card ι : ℝ) ≤ μ^2 * ((1+2/q)^m-1)) :
    (∑ i, (g * energy i + 64 * deviation i) / μ^2) / (Fintype.card ι : ℝ) ≤ 373/336 := by
  let B := (1+2/q)^m + 4*(2/q)^m
  let V := (1+2/q)^m-1
  have hn0 : 0 < n := by linarith
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq0 : 0 < q := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgn' : g/n ≤ 8193/8192 := (div_le_iff₀ hn0).mpr (by linarith)
  have hgμ : g/μ ≤ 1/16 := (div_le_iff₀ hμ).mpr (by linarith)
  calc
    _ = (g * ((∑ i, energy i) / (Fintype.card ι : ℝ)) +
        64 * ((∑ i, deviation i) / (Fintype.card ι : ℝ))) / μ^2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ (g * (μ + μ^2/n * B) + 64 * (μ^2 * V)) / μ^2 := by gcongr
    _ = g/μ + g/n*B + 64*V := by field_simp <;> ring
    _ ≤ 1/16 + (8193/8192 : ℝ)*B + 64*V := by gcongr
    _ ≤ _ := collision_budget m hm hq

set_option maxHeartbeats 600000 in
theorem solution :
    (∀ (p m : ℕ) [Fact p.Prime], 3 < p → 2 ≤ m →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        64 ≤ gord → 4096 * m ≤ n →
        let T := hashThreshold p n m gord
        let μ := (qBlk p n T) ^ m
        (∑ S : ECSeed p m, collisionPotentialAdd μ (ecFactorBlock E T S)) /
          (Fintype.card (ECSeed p m) : ℝ) ≤ (373 : ℝ) / 336) ∧
    (∀ (p m : ℕ) [Fact p.Prime], 2 ≤ m →
      let gord := p - 1
      let n := p - 1
      64 ≤ gord → 4096 * m ≤ n →
      let T := hashThreshold p n m gord
      let μ := (qBlk p n T) ^ m
      (∑ S : FpSeed p m, collisionPotentialMul μ (fpFactorBlock (p := p) T S)) /
        (Fintype.card (FpSeed p m) : ℝ) ≤ (373 : ℝ) / 336) := by
  constructor
  · intro p m hp hp3 hm E hE
    intro g n hg hn
    letI := ecPointFintype E
    let T := hashThreshold p n m g
    let q := qBlk p n T
    obtain ⟨hq, hdiag⟩ := parameter_lower_bounds p n m g (Nat.Prime.pos hp.out) (by omega) hm
    have hn' : (8192 : ℝ) ≤ n := by exact_mod_cast (show 8192 ≤ n by omega)
    have hgn : (g : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (show g ≤ n+1 by omega)
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hq' : 4096 * (m : ℝ) ≤ q := hq
    have hq0 : 0 < q := by linarith
    exact combine_moments (ι := ECSeed p m) m hm g n q (q^m) (Nat.cast_nonneg _) hn' hgn hq' (pow_pos hq0 _) hdiag
      (fun S => (collisionEnergyAdd (ecFactorBlock E T S) : ℝ))
      (fun S => ((productSize (ecFactorBlock E T S) : ℝ) - q^m)^2)
      (collision_energy_moment_bound.1 p m hp3 hm E hg hn)
      (collision_variance_moment_bound.1 p m hp3 hm E hg hn)
  · intro p m hp hm g n hg hn
    let T := hashThreshold p n m n
    let q := qBlk p n T
    obtain ⟨hq, hdiag⟩ := parameter_lower_bounds p n m n (Nat.Prime.pos hp.out) (by omega) hm
    have hn' : (8192 : ℝ) ≤ n := by exact_mod_cast (show 8192 ≤ n by omega)
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hq' : 4096 * (m : ℝ) ≤ q := hq
    have hq0 : 0 < q := by linarith
    have hcard : Fintype.card (ZMod p)ˣ = n := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
    simp only [collisionPotentialMul, hcard]
    exact combine_moments (ι := FpSeed p m) m hm n n q (q^m) (Nat.cast_nonneg _) hn' (by linarith) hq' (pow_pos hq0 _) hdiag
      (fun S => (collisionEnergyMul (fpFactorBlock (p := p) T S) : ℝ))
      (fun S => ((productSize (fpFactorBlock (p := p) T S) : ℝ) - q^m)^2)
      (collision_energy_moment_bound.2 p m hm hg hn)
      (collision_variance_moment_bound.2 p m hm hg hn)
