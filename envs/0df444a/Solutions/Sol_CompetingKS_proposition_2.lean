-- Prove2me | solution 1 for CompetingKS.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T15:58:14.785497+00:00
-- url     : https://prove2.me/submissions/bec48a4c-5000-4d19-8c64-6431fe84185a

import Definitions.Def_CompetingKS_unitOT
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Pointwise

set_option autoImplicit false


set_option autoImplicit false

noncomputable section
namespace S11Pareto
open CompetingKS

private theorem ot_den_pos {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    0 < 4 - η ^ 2 := by nlinarith

private theorem to_den_pos {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    0 < 1 - η ^ 2 := by nlinarith

theorem qOT_closed_general {a b η x y : ℝ} (hb0 : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hc : InCHat a η x y) :
    qOT a b η x y = (2 * (a - x) - η * (a - y)) / (b * (4 - η ^ 2)) := by
  have hd := ne_of_gt (ot_den_pos hη0 hη1)
  have hb := ne_of_gt hb0
  rcases hc with ⟨hc1, hc2⟩
  unfold qOT
  split_ifs with h1 h2
  · have hz : 2 * (a - x) - η * (a - y) = 0 := by linarith
    simp [hz]
  · have he : 2 * (a - y) = η * (a - x) := by linarith
    have he' := congrArg (fun t : ℝ => η * t) he
    field_simp
    nlinarith
  · rfl

theorem qTO_closed_general {a b η x y : ℝ} (hb0 : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hc : InCCheck a η x y) :
    qTO a b η x y = ((a - x) - η * (a - y)) / (2 * b * (1 - η ^ 2)) := by
  have hd := ne_of_gt (to_den_pos hη0 hη1)
  have hb := ne_of_gt hb0
  rcases hc with ⟨hc1, hc2⟩
  unfold qTO
  split_ifs with h1 h2
  · have hz : (a - x) - η * (a - y) = 0 := by linarith
    simp [hz]
  · have he : a - y = η * (a - x) := by linarith
    have he' := congrArg (fun t : ℝ => η * t) he
    field_simp
    nlinarith
  · rfl

private theorem qOT_closed {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hc : InCHat 1 η x y) :
    qOT 1 1 η x y = (2 * (1 - x) - η * (1 - y)) / (4 - η ^ 2) := by
  have hd := ne_of_gt (ot_den_pos hη0 hη1)
  rcases hc with ⟨hc1, hc2⟩
  unfold qOT
  split_ifs with h1 h2
  · have hz : 2 * (1 - x) - η * (1 - y) = 0 := by linarith
    simp [hz]
  · have hb : 2 * (1 - y) = η * (1 - x) := by linarith
    have hb' := congrArg (fun t : ℝ => η * t) hb
    field_simp
    nlinarith
  · simp

private theorem qTO_closed {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hc : InCCheck 1 η x y) :
    qTO 1 1 η x y = ((1 - x) - η * (1 - y)) / (2 * (1 - η ^ 2)) := by
  have hd := ne_of_gt (to_den_pos hη0 hη1)
  rcases hc with ⟨hc1, hc2⟩
  unfold qTO
  split_ifs with h1 h2
  · have hz : (1 - x) - η * (1 - y) = 0 := by linarith
    simp [hz]
  · have hb : 1 - y = η * (1 - x) := by linarith
    have hb' := congrArg (fun t : ℝ => η * t) hb
    field_simp
    nlinarith
  · simp

private def otS (η x y : ℝ) : ℝ :=
  (x * (2 * (1 - x) - η * (1 - y)) +
   y * (2 * (1 - y) - η * (1 - x))) / (4 - η ^ 2)

private def otB (η x y : ℝ) : ℝ :=
  ((2 * (1 - x) - η * (1 - y)) / (4 - η ^ 2)) ^ 2

private def toS (η x y : ℝ) : ℝ :=
  x * ((1 - x) - η * (1 - y)) / (2 * (1 - η ^ 2))

private def toB (η x y : ℝ) : ℝ :=
  ((1 - x) ^ 2 + (1 - y) ^ 2 - 2 * η * (1 - x) * (1 - y)) /
    (4 * (1 - η ^ 2))

private theorem ot_profits_closed {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hc : InCHat 1 η x y) :
    (normOT η y).S x = otS η x y ∧ (normOT η y).B x = otB η x y := by
  have hd := ne_of_gt (ot_den_pos hη0 hη1)
  have hc' : InCHat 1 η y x := ⟨hc.2, hc.1⟩
  constructor
  · change supplierOT 1 1 0 η x y = _
    unfold supplierOT ROT otS
    rw [qOT_closed hη0 hη1 hc, qOT_closed hη0 hη1 hc']
    ring
  · change retailerOT 1 1 η x y = _
    unfold retailerOT rOT priceOT price otB
    rw [qOT_closed hη0 hη1 hc, qOT_closed hη0 hη1 hc']
    field_simp
    ring

private theorem to_profits_closed {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hc : InCCheck 1 η x y) :
    (normTO η y).S x = toS η x y ∧ (normTO η y).B x = toB η x y := by
  have hd := ne_of_gt (to_den_pos hη0 hη1)
  have hc' : InCCheck 1 η y x := ⟨hc.2, hc.1⟩
  constructor
  · change supplierTO 1 1 0 η x y = _
    unfold supplierTO RTO toS
    rw [qTO_closed hη0 hη1 hc]
    ring
  · change retailerTO 1 1 η x y = _
    unfold retailerTO rTO priceTO price toB
    rw [qTO_closed hη0 hη1 hc, qTO_closed hη0 hη1 hc']
    field_simp
    ring

private theorem ot_profits_monopoly {η x y : ℝ}
    (ho : η * (1 - y) < 2 * (1 - x))
    (hz : 2 * (1 - y) ≤ η * (1 - x)) :
    (normOT η y).S x = x * (1 - x) / 2 ∧
    (normOT η y).B x = (1 - x) ^ 2 / 4 := by
  have hqx : qOT 1 1 η x y = (1 - x) / 2 := by
    simp [qOT, not_le.mpr ho, hz]
  have hqy : qOT 1 1 η y x = 0 := by simp [qOT, hz]
  constructor
  · change supplierOT 1 1 0 η x y = _
    simp [supplierOT, ROT, hqx, hqy]
    ring
  · change retailerOT 1 1 η x y = _
    simp [retailerOT, rOT, priceOT, price, hqx, hqy]
    ring

private theorem to_profits_monopoly {η x y : ℝ}
    (ho : η * (1 - y) < 1 - x)
    (hz : 1 - y ≤ η * (1 - x)) :
    (normTO η y).S x = x * (1 - x) / 2 ∧
    (normTO η y).B x = (1 - x) ^ 2 / 4 := by
  have hqx : qTO 1 1 η x y = (1 - x) / 2 := by
    simp [qTO, not_le.mpr ho, hz]
  have hqy : qTO 1 1 η y x = 0 := by simp [qTO, hz]
  constructor
  · change supplierTO 1 1 0 η x y = _
    simp [supplierTO, RTO, hqx]
    ring
  · change retailerTO 1 1 η x y = _
    simp [retailerTO, rTO, priceTO, price, hqx, hqy]
    ring

private theorem otS_difference (η x y z : ℝ) :
    otS η z y - otS η x y =
      (x - z) * (2 * (x + z) - (2 - η + 2 * η * y)) / (4 - η ^ 2) := by
  unfold otS
  ring

/-- At a maximum price above one half, lowering the price gives a dominating allocation. -/
theorem ot_strict_dominator_of_large_max {η x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (_hy0 : 0 ≤ y) (_hy1 : y ≤ 1)
    (hxy : y ≤ x) (hc : InCHat 1 η x y) (hx : 1 / 2 < x) :
    ∃ z ∈ Set.Icc (0 : ℝ) 1,
      (normOT η y).S x < (normOT η y).S z ∧ (normOT η y).B x < (normOT η y).B z := by
  let z : ℝ := (x + 1 / 2) / 2
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hzx : z < x := by dsimp [z]; linarith
  have hzo : η * (1 - y) < 2 * (1 - z) := by
    have := hc.1
    linarith
  have hd : 0 < 4 - η ^ 2 := ot_den_pos hη0 hη1
  have hbr : 0 < 2 * (x + z) - (2 - η + 2 * η * y) := by
    have hp := mul_nonneg (show 0 ≤ 1 - η by linarith) (show 0 ≤ x - 1 / 2 by linarith)
    have hp' := mul_nonneg hη0 (sub_nonneg.mpr hxy)
    dsimp [z]
    nlinarith
  have hS : otS η x y < otS η z y := by
    have hp := div_pos (mul_pos (sub_pos.mpr hzx) hbr) hd
    rw [← otS_difference] at hp
    linarith
  have hpx := ot_profits_closed hη0 hη1 hc
  have hqx0 : 0 ≤ (2 * (1 - x) - η * (1 - y)) / (4 - η ^ 2) :=
    div_nonneg (sub_nonneg.mpr hc.1) hd.le
  by_cases hcut : 2 * (1 - y) ≤ η * (1 - z)
  · have hpz := ot_profits_monopoly hzo hcut
    have hfac : 0 ≤ y - η * z / 2 := by nlinarith
    have he : z * (1 - z) / 2 - otS η z y =
        (η * (1 - z) - 2 * (1 - y)) * (y - η * z / 2) / (4 - η ^ 2) := by
      unfold otS
      field_simp
      ring
    have hmono : otS η z y ≤ z * (1 - z) / 2 := by
      have hp := div_nonneg (mul_nonneg (sub_nonneg.mpr hcut) hfac) hd.le
      rw [← he] at hp
      linarith
    have hqbound : (2 * (1 - x) - η * (1 - y)) / (4 - η ^ 2) ≤ (1 - x) / 2 := by
      apply (div_le_iff₀ hd).2
      have hp := mul_nonneg hη0 (sub_nonneg.mpr hc.2)
      nlinarith
    have hB : otB η x y < (1 - z) ^ 2 / 4 := by
      unfold otB
      nlinarith
    refine ⟨z, ⟨hz0, hz1⟩, ?_, ?_⟩
    · rw [hpx.1, hpz.1]
      exact hS.trans_le hmono
    · rw [hpx.2, hpz.2]
      exact hB
  · have hcz : InCHat 1 η z y := ⟨hzo.le, le_of_lt (not_le.mp hcut)⟩
    have hpz := ot_profits_closed hη0 hη1 hcz
    have hq : (2 * (1 - x) - η * (1 - y)) / (4 - η ^ 2) <
        (2 * (1 - z) - η * (1 - y)) / (4 - η ^ 2) := by
      apply (div_lt_div_iff_of_pos_right hd).2
      linarith
    have hB : otB η x y < otB η z y := by
      unfold otB
      nlinarith
    refine ⟨z, ⟨hz0, hz1⟩, ?_, ?_⟩
    · rw [hpx.1, hpz.1]
      exact hS
    · rw [hpx.2, hpz.2]
      exact hB

theorem ot_dominated_of_large_max {η x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : y ≤ x) (hc : InCHat 1 η x y) (hx : 1 / 2 < x) :
    (normOT η y).IsDominated x := by
  obtain ⟨z, hz, hS, hB⟩ := ot_strict_dominator_of_large_max hη0 hη1 hx0 hx1 hy0 hy1 hxy hc hx
  exact ⟨z, hz, hS.le, hB.le, Or.inl hS⟩

/-- The normalized OT equilibrium cutoff uses Pareto optimality only. -/
theorem ot_pareto_max_le_half {η x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hxy : y ≤ x) (hc : InCHat 1 η x y)
    (hp : (normOT η y).IsPareto x) : x ≤ 1 / 2 := by
  by_contra hx
  exact hp.2 (ot_dominated_of_large_max hη0 hη1 hp.1.1 hp.1.2 hy.1 hy.2
    hxy hc (not_le.mp hx))

private theorem toS_difference (η x y z : ℝ) :
    toS η z y - toS η x y =
      (x - z) * (x + z - (1 - η + η * y)) / (2 * (1 - η ^ 2)) := by
  unfold toS
  ring

private theorem toB_difference (η x y z : ℝ) :
    toB η z y - toB η x y =
      (x - z) * ((1 - x) - η * (1 - y) + (1 - z) - η * (1 - y)) /
        (4 * (1 - η ^ 2)) := by
  unfold toB
  ring

/-- At a maximum price above the TO cutoff, a lower price gives a dominating allocation. -/
theorem to_strict_dominator_of_large_max {η x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (_hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : y ≤ x) (hc : InCCheck 1 η x y)
    (hx : (1 - η) / (2 - η) < x) :
    ∃ z ∈ Set.Icc (0 : ℝ) 1,
      (normTO η y).S x < (normTO η y).S z ∧ (normTO η y).B x < (normTO η y).B z := by
  let T : ℝ := (1 - η) / (2 - η)
  let z : ℝ := (x + T) / 2
  have hd0 : 0 < 2 - η := by linarith
  have hd1 : 0 < 1 + η := by linarith
  have hd : 0 < 1 - η ^ 2 := to_den_pos hη0 hη1
  have hT0 : 0 ≤ T := div_nonneg (by linarith) hd0.le
  have hT1 : T ≤ 1 := by
    dsimp [T]
    apply (div_le_iff₀ hd0).2
    linarith
  have hT : (2 - η) * T = 1 - η := by
    dsimp [T]
    field_simp
  have hTx : T < x := hx
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : z ≤ 1 := by dsimp [z]; linarith
  have hzx : z < x := by dsimp [z]; linarith
  have hzo : η * (1 - y) < 1 - z := by have := hc.1; linarith
  have hbr : 0 < x + z - (1 - η + η * y) := by
    have hp := mul_pos (show 0 < 3 / 2 - η by linarith) (sub_pos.mpr hTx)
    have hp' := mul_nonneg hη0 (sub_nonneg.mpr hxy)
    dsimp [z]
    nlinarith only [hT, hp, hp']
  have hS : toS η x y < toS η z y := by
    have hp : 0 < (x - z) * (x + z - (1 - η + η * y)) / (2 * (1 - η ^ 2)) :=
      div_pos (mul_pos (sub_pos.mpr hzx) hbr) (mul_pos (by norm_num) hd)
    rw [← toS_difference] at hp
    linarith only [hp]
  have hpx := to_profits_closed hη0 hη1 hc
  by_cases hcut : 1 - y ≤ η * (1 - z)
  · have hpz := to_profits_monopoly hzo hcut
    have heS : x * (1 - x) / (2 * (1 + η)) - toS η x y =
        η * x * (x - y) / (2 * (1 - η ^ 2)) := by
      unfold toS
      field_simp
      ring
    have hSbound : toS η x y ≤ x * (1 - x) / (2 * (1 + η)) := by
      have hp : 0 ≤ η * x * (x - y) / (2 * (1 - η ^ 2)) :=
        div_nonneg (mul_nonneg (mul_nonneg hη0 hx0) (sub_nonneg.mpr hxy))
          (mul_nonneg (by norm_num) hd.le)
      rw [← heS] at hp
      linarith only [hp]
    have hresid : 0 ≤ 1 / (2 - η) - (x - T) := by
      have he : 1 / (2 - η) + T = 1 := by
        dsimp [T]
        field_simp
        ring
      linarith only [he, hx1]
    have hid : (1 + η) * z * (1 - z) - x * (1 - x) =
        (3 - η) / 4 * (x - T) ^ 2 +
        (η * (1 - η) / (2 * (2 - η))) * (1 / (2 - η) - (x - T)) +
        η * (1 - η) / (2 * (2 - η) ^ 2) := by
      dsimp [z, T]
      field_simp
      ring
    have hF : 0 < (1 + η) * z * (1 - z) - x * (1 - x) := by
      rw [hid]
      have hp1 : 0 < (3 - η) / 4 * (x - T) ^ 2 :=
        mul_pos (div_pos (by linarith only [hη1]) (by norm_num)) (sq_pos_of_pos (sub_pos.mpr hTx))
      have hp2 : 0 ≤ (η * (1 - η) / (2 * (2 - η))) *
          (1 / (2 - η) - (x - T)) :=
        mul_nonneg (div_nonneg (mul_nonneg hη0 (by linarith only [hη1]))
          (mul_nonneg (by norm_num) hd0.le)) hresid
      have hp3 : 0 ≤ η * (1 - η) / (2 * (2 - η) ^ 2) :=
        div_nonneg (mul_nonneg hη0 (by linarith only [hη1])) (by positivity)
      linarith only [hp1, hp2, hp3]
    have hSm : x * (1 - x) / (2 * (1 + η)) < z * (1 - z) / 2 := by
      apply (div_lt_div_iff₀ (mul_pos (by norm_num) hd1) (by norm_num)).2
      nlinarith only [hF]
    have heB : (1 - y) ^ 2 / (2 * (1 + η)) - toB η x y =
        (x - y) * ((1 - x) - η * (1 - y) + (1 - η) * (1 - y)) /
          (4 * (1 - η ^ 2)) := by
      unfold toB
      field_simp
      ring
    have hBbound : toB η x y ≤ (1 - y) ^ 2 / (2 * (1 + η)) := by
      have hp : 0 ≤ (x - y) * ((1 - x) - η * (1 - y) + (1 - η) * (1 - y)) /
          (4 * (1 - η ^ 2)) :=
        div_nonneg (mul_nonneg (sub_nonneg.mpr hxy)
          (add_nonneg (sub_nonneg.mpr hc.1)
            (mul_nonneg (by linarith only [hη1]) (by linarith only [hy1]))))
          (mul_nonneg (by norm_num) hd.le)
      rw [← heB] at hp
      linarith only [hp]
    have hsq : (1 - y) ^ 2 ≤ (η * (1 - z)) ^ 2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hcut)
        (add_nonneg (show 0 ≤ η * (1 - z) by positivity) (show 0 ≤ 1 - y by linarith))
      nlinarith only [hp]
    have hecoeff : 2 * η ^ 2 < 1 + η := by
      have hp := mul_pos (show 0 < 1 - η by linarith only [hη1])
        (show 0 < 1 + 2 * η by linarith only [hη0])
      nlinarith only [hp]
    have hBm : (1 - y) ^ 2 / (2 * (1 + η)) < (1 - z) ^ 2 / 4 := by
      apply (div_lt_div_iff₀ (mul_pos (by norm_num) hd1) (by norm_num)).2
      have hp := mul_pos (sub_pos.mpr hecoeff)
        (sq_pos_of_pos (show 0 < 1 - z by linarith only [hzx, hx1]))
      nlinarith only [hp, hsq]
    refine ⟨z, ⟨hz0, hz1⟩, ?_, ?_⟩
    · rw [hpx.1, hpz.1]
      exact hSbound.trans_lt hSm
    · rw [hpx.2, hpz.2]
      exact hBbound.trans_lt hBm
  · have hcz : InCCheck 1 η z y := ⟨hzo.le, le_of_lt (not_le.mp hcut)⟩
    have hpz := to_profits_closed hη0 hη1 hcz
    have hB : toB η x y < toB η z y := by
      have hp : 0 < (x - z) * ((1 - x) - η * (1 - y) + (1 - z) - η * (1 - y)) /
          (4 * (1 - η ^ 2)) :=
        div_pos (mul_pos (sub_pos.mpr hzx)
          (by linarith only [hc.1, hzo])) (mul_pos (by norm_num) hd)
      rw [← toB_difference] at hp
      linarith only [hp]
    refine ⟨z, ⟨hz0, hz1⟩, ?_, ?_⟩
    · rw [hpx.1, hpz.1]
      exact hS
    · rw [hpx.2, hpz.2]
      exact hB

theorem to_dominated_of_large_max {η x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : y ≤ x) (hc : InCCheck 1 η x y)
    (hx : (1 - η) / (2 - η) < x) : (normTO η y).IsDominated x := by
  obtain ⟨z, hz, hS, hB⟩ := to_strict_dominator_of_large_max hη0 hη1 hx0 hx1 hy0 hy1 hxy hc hx
  exact ⟨z, hz, hS.le, hB.le, Or.inl hS⟩

/-- The normalized TO equilibrium cutoff uses Pareto optimality only. -/
theorem to_pareto_max_le {η x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hxy : y ≤ x) (hc : InCCheck 1 η x y)
    (hp : (normTO η y).IsPareto x) : x ≤ (1 - η) / (2 - η) := by
  by_contra hx
  exact hp.2 (to_dominated_of_large_max hη0 hη1 hp.1.1 hp.1.2 hy.1 hy.2
    hxy hc (not_le.mp hx))

end S11Pareto
end



set_option autoImplicit false
noncomputable section
open CompetingKS

namespace S11CanonicalKS

/-- A quadratic bargaining frontier, including the zero-allocation tail. -/
structure Shape (U : BargainingUnit) (ℓ H α β : ℝ) : Prop where
  interval_pos : ℓ < H
  seller_scale_pos : 0 < α
  buyer_scale_pos : 0 < β
  interval_mem : ∀ w, ℓ ≤ w → w ≤ H → w ∈ U.W
  seller : ∀ w ∈ U.W, U.S w - U.D =
    if w ≤ H then α * (H - w) * (w - ℓ) else 0
  buyer : ∀ w ∈ U.W, U.B w - U.d =
    if w ≤ H then β * (H - w) ^ 2 else 0

theorem sbar_eq_of_maximizer {U : BargainingUnit} {x : ℝ}
    (hx : U.IsSMaximizer x) : U.Sbar = U.S x := by
  have hmem : U.S x ∈ U.S '' {w ∈ U.W | U.d ≤ U.B w} :=
    ⟨x, ⟨hx.1, hx.2.1⟩, rfl⟩
  have hub : ∀ y ∈ U.S '' {w ∈ U.W | U.d ≤ U.B w}, y ≤ U.S x := by
    rintro y ⟨w, hw, rfl⟩
    exact hx.2.2 w hw.1 hw.2
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

theorem bbar_eq_of_maximizer {U : BargainingUnit} {x : ℝ}
    (hx : U.IsBMaximizer x) : U.Bbar = U.B x := by
  have hmem : U.B x ∈ U.B '' {w ∈ U.W | U.D ≤ U.S w} :=
    ⟨x, ⟨hx.1, hx.2.1⟩, rfl⟩
  have hub : ∀ y ∈ U.B '' {w ∈ U.W | U.D ≤ U.S w}, y ≤ U.B x := by
    rintro y ⟨w, hw, rfl⟩
    exact hx.2.2 w hw.1 hw.2
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

variable {U : BargainingUnit} {ℓ H α β : ℝ} (h : Shape U ℓ H α β)

include h

theorem Shape.buyer_nonneg (w : ℝ) (hw : w ∈ U.W) : 0 ≤ U.B w - U.d := by
  rw [h.buyer w hw]
  split
  · exact mul_nonneg h.buyer_scale_pos.le (sq_nonneg _)
  · exact le_rfl

theorem Shape.ir_iff (w : ℝ) : U.IsIR w ↔ w ∈ U.W ∧ ℓ ≤ w := by
  constructor
  · rintro ⟨hw, hS, hB⟩
    refine ⟨hw, ?_⟩
    by_contra hn
    have hwℓ : w < ℓ := lt_of_not_ge hn
    have hwH : w < H := hwℓ.trans h.interval_pos
    have hs := h.seller w hw
    rw [if_pos hwH.le] at hs
    have hneg := mul_neg_of_pos_of_neg
      (mul_pos h.seller_scale_pos (sub_pos.mpr hwH)) (sub_neg.mpr hwℓ)
    linarith
  · rintro ⟨hw, hwℓ⟩
    refine ⟨hw, ?_, sub_nonneg.mp (h.buyer_nonneg w hw)⟩
    apply sub_nonneg.mp
    rw [h.seller w hw]
    split
    · exact mul_nonneg (mul_nonneg h.seller_scale_pos.le
        (sub_nonneg.mpr ‹w ≤ H›)) (sub_nonneg.mpr hwℓ)
    · exact le_rfl

theorem Shape.seller_bound (w : ℝ) (hw : w ∈ U.W) :
    U.S w - U.D ≤ α * (H - ℓ) ^ 2 / 4 := by
  rw [h.seller w hw]
  split
  · have hq : (H - w) * (w - ℓ) ≤ (H - ℓ) ^ 2 / 4 := by
      nlinarith [sq_nonneg (2 * w - H - ℓ)]
    have hm := mul_le_mul_of_nonneg_left hq h.seller_scale_pos.le
    nlinarith
  · exact div_nonneg (mul_nonneg h.seller_scale_pos.le (sq_nonneg _)) (by norm_num)

theorem Shape.buyer_bound (w : ℝ) (hw : w ∈ U.W) (hS : U.D ≤ U.S w) :
    U.B w - U.d ≤ β * (H - ℓ) ^ 2 := by
  have hwℓ := ((h.ir_iff w).mp
    ⟨hw, hS, sub_nonneg.mp (h.buyer_nonneg w hw)⟩).2
  rw [h.buyer w hw]
  split
  · have hwH : w ≤ H := ‹w ≤ H›
    have hq : (H - w) ^ 2 ≤ (H - ℓ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hwℓ)
        (show 0 ≤ 2 * H - w - ℓ by linarith)]
    exact mul_le_mul_of_nonneg_left hq h.buyer_scale_pos.le
  · exact mul_nonneg h.buyer_scale_pos.le (sq_nonneg _)

theorem Shape.seller_maximizer : U.IsSMaximizer ((ℓ + H) / 2) := by
  have hw : (ℓ + H) / 2 ∈ U.W := h.interval_mem _ (by linarith [h.interval_pos])
    (by linarith [h.interval_pos])
  refine ⟨hw, sub_nonneg.mp (h.buyer_nonneg _ hw), ?_⟩
  intro w hw' _
  have hb := h.seller_bound w hw'
  have he := h.seller ((ℓ + H) / 2) hw
  rw [if_pos (by linarith [h.interval_pos])] at he
  nlinarith

theorem Shape.buyer_maximizer : U.IsBMaximizer ℓ := by
  have hw : ℓ ∈ U.W := h.interval_mem _ le_rfl h.interval_pos.le
  have he := h.seller ℓ hw
  simp only [if_pos h.interval_pos.le, sub_self, mul_zero] at he
  refine ⟨hw, by linarith, ?_⟩
  intro w hw' hS
  have hb := h.buyer_bound w hw' hS
  have hm := h.buyer ℓ hw
  rw [if_pos h.interval_pos.le] at hm
  linarith

theorem Shape.sbar_surplus : U.Sbar - U.D = α * (H - ℓ) ^ 2 / 4 := by
  rw [sbar_eq_of_maximizer h.seller_maximizer]
  rw [h.seller _ h.seller_maximizer.1, if_pos (by linarith [h.interval_pos])]
  ring

theorem Shape.bbar_surplus : U.Bbar - U.d = β * (H - ℓ) ^ 2 := by
  rw [bbar_eq_of_maximizer h.buyer_maximizer]
  rw [h.buyer _ h.buyer_maximizer.1, if_pos h.interval_pos.le]

def ksPrice (ℓ H : ℝ) : ℝ := ℓ + (H - ℓ) / 5

theorem Shape.ksPrice_mem : ksPrice ℓ H ∈ U.W :=
  h.interval_mem _ (by unfold ksPrice; linarith [h.interval_pos])
    (by unfold ksPrice; linarith [h.interval_pos])

theorem Shape.ksPrice_surplus_pos :
    0 < U.S (ksPrice ℓ H) - U.D ∧ 0 < U.B (ksPrice ℓ H) - U.d := by
  have hL : ℓ < ksPrice ℓ H := by unfold ksPrice; linarith [h.interval_pos]
  have hH : ksPrice ℓ H < H := by unfold ksPrice; linarith [h.interval_pos]
  rw [h.seller _ h.ksPrice_mem, h.buyer _ h.ksPrice_mem,
    if_pos hH.le, if_pos hH.le]
  exact ⟨mul_pos (mul_pos h.seller_scale_pos (sub_pos.mpr hH)) (sub_pos.mpr hL),
    mul_pos h.buyer_scale_pos (sq_pos_of_pos (sub_pos.mpr hH))⟩

omit h in
theorem pareto_of_weighted_maximum (U : BargainingUnit) (x p q : ℝ)
    (hx : x ∈ U.W) (hp : 0 < p) (hq : 0 < q)
    (hm : ∀ w ∈ U.W, p * (U.S w - U.D) + q * (U.B w - U.d) ≤
      p * (U.S x - U.D) + q * (U.B x - U.d)) : U.IsPareto x := by
  refine ⟨hx, ?_⟩
  rintro ⟨w, hw, hS, hB, hs | hb⟩
  · have he := add_lt_add_of_lt_of_le
      (mul_lt_mul_of_pos_left (sub_lt_sub_right hs U.D) hp)
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hB U.d) hq.le)
    exact (not_lt_of_ge (hm w hw)) he
  · have he := add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hS U.D) hp.le)
      (mul_lt_mul_of_pos_left (sub_lt_sub_right hb U.d) hq)
    exact (not_lt_of_ge (hm w hw)) he

theorem Shape.ksPrice_pareto : U.IsPareto (ksPrice ℓ H) := by
  have hα := h.seller_scale_pos
  have hβ := h.buyer_scale_pos
  apply pareto_of_weighted_maximum U (ksPrice ℓ H) (8 * β) (3 * α)
    h.ksPrice_mem (by positivity) (by positivity)
  intro w hw
  have hH : ksPrice ℓ H ≤ H := by unfold ksPrice; linarith [h.interval_pos]
  rw [h.seller _ hw, h.buyer _ hw, h.seller _ h.ksPrice_mem,
    h.buyer _ h.ksPrice_mem, if_pos hH]
  simp only [if_pos hH]
  by_cases hwH : w ≤ H
  · rw [if_pos hwH, if_pos hwH]
    have hid :
        8 * β * (α * (H - ksPrice ℓ H) * (ksPrice ℓ H - ℓ)) +
          3 * α * (β * (H - ksPrice ℓ H) ^ 2) -
        (8 * β * (α * (H - w) * (w - ℓ)) + 3 * α * (β * (H - w) ^ 2)) =
        5 * α * β * (w - ksPrice ℓ H) ^ 2 := by unfold ksPrice; ring
    have hn : 0 ≤ 5 * α * β * (w - ksPrice ℓ H) ^ 2 := by positivity
    linarith
  · rw [if_neg hwH, if_neg hwH]
    have hs := h.ksPrice_surplus_pos
    rw [h.seller _ h.ksPrice_mem, h.buyer _ h.ksPrice_mem, if_pos hH] at hs
    simp only [if_pos hH] at hs
    have h1 := mul_nonneg (show 0 ≤ 8 * β by positivity) hs.1.le
    have h2 := mul_nonneg (show 0 ≤ 3 * α by positivity) hs.2.le
    simpa using add_nonneg h1 h2

theorem Shape.surpluses_zero_of_ge (w : ℝ) (hw : w ∈ U.W) (hwH : H ≤ w) :
    U.S w - U.D = 0 ∧ U.B w - U.d = 0 := by
  rw [h.seller w hw, h.buyer w hw]
  by_cases hle : w ≤ H
  · have : w = H := le_antisymm hle hwH
    subst w
    simp
  · simp [hle]

theorem Shape.pareto_lt (w : ℝ) (hw : U.IsPareto w) : w < H := by
  by_contra hn
  obtain ⟨hS, hB⟩ := h.surpluses_zero_of_ge w hw.1 (le_of_not_gt hn)
  obtain ⟨hs, hb⟩ := h.ksPrice_surplus_pos
  apply hw.2
  exact ⟨ksPrice ℓ H, h.ksPrice_mem, by linarith, by linarith, Or.inl (by linarith)⟩

theorem Shape.ks_iff (w : ℝ) : U.IsKSResponse w ↔ w = ksPrice ℓ H := by
  constructor
  · rintro ⟨hir, hp, he⟩
    have hwH := h.pareto_lt w hp
    rw [h.sbar_surplus, h.bbar_surplus, h.seller w hir.1,
      h.buyer w hir.1, if_pos hwH.le] at he
    simp only [if_pos hwH.le] at he
    have hf : (α * β * (H - w) * (H - ℓ) ^ 2) *
        ((H - w) - 4 * (w - ℓ)) = 0 := by
      linear_combination 4 * he
    have hn : α * β * (H - w) * (H - ℓ) ^ 2 ≠ 0 := by
      exact ne_of_gt (mul_pos (mul_pos (mul_pos h.seller_scale_pos h.buyer_scale_pos)
        (sub_pos.mpr hwH)) (sq_pos_of_pos (sub_pos.mpr h.interval_pos)))
    have hz := (mul_eq_zero.mp hf).resolve_left hn
    unfold ksPrice
    linarith
  · rintro rfl
    refine ⟨(h.ir_iff _).mpr ⟨h.ksPrice_mem, ?_⟩, h.ksPrice_pareto, ?_⟩
    · unfold ksPrice; linarith [h.interval_pos]
    · have hwH : ksPrice ℓ H ≤ H := by unfold ksPrice; linarith [h.interval_pos]
      rw [h.sbar_surplus, h.bbar_surplus, h.seller _ h.ksPrice_mem,
        h.buyer _ h.ksPrice_mem, if_pos hwH]
      simp only [if_pos hwH]
      unfold ksPrice
      ring

end S11CanonicalKS
end


set_option autoImplicit false
noncomputable section
open CompetingKS S11CanonicalKS S11Pareto

namespace S11CanonicalUnits

def otLower (c η y : ℝ) : ℝ := c + η * (y - c) / 2
def otUpper (a η y : ℝ) : ℝ := a - η * (a - y) / 2
def otAlpha (b η : ℝ) : ℝ := 2 / (b * (4 - η ^ 2))
def otBeta (b η : ℝ) : ℝ := 4 / (b * (4 - η ^ 2) ^ 2)
def toUpper (a η y : ℝ) : ℝ := a - η * (a - y)
def toAlpha (b η : ℝ) : ℝ := 1 / (2 * b * (1 - η ^ 2))
def toBeta (b η : ℝ) : ℝ := 1 / (4 * b * (1 - η ^ 2))

theorem disagreeOT_formula {a b c η y : ℝ} (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hya : y ≤ a) :
    disagreeOT a b c η y = (a - y) * (y - c) / (2 * b) := by
  have hd : 0 < 4 - η ^ 2 := by nlinarith
  have hc : InCHat a η y (otUpper a η y) := by
    constructor
    · dsimp [otUpper]
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hya)]
    · dsimp [otUpper]
      linarith
  change qOT a b η y (otUpper a η y) * (y - c) = _
  rw [qOT_closed_general hb hη0 hη1 hc]
  unfold otUpper
  field_simp
  ring

theorem disagreeTO_formula {a b η y : ℝ} (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hya : y ≤ a) :
    disagreeTO a b η y = (a - y) ^ 2 / (4 * b) := by
  have hd : 0 < 1 - η ^ 2 := by nlinarith
  have hc : InCCheck a η y (toUpper a η y) := by
    constructor
    · dsimp [toUpper]
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hya)]
    · dsimp [toUpper]
      linarith
  have hc' : InCCheck a η (toUpper a η y) y := ⟨hc.2, hc.1⟩
  change rTO a b η y (toUpper a η y) = _
  unfold rTO priceTO price
  rw [qTO_closed_general hb hη0 hη1 hc, qTO_closed_general hb hη0 hη1 hc']
  unfold toUpper
  field_simp
  ring

theorem ot_surpluses_closed {a b c η w y : ℝ} (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hya : y ≤ a) (hc : InCHat a η w y) :
    (unitOT a b c η y).S w - (unitOT a b c η y).D =
      otAlpha b η * (otUpper a η y - w) * (w - otLower c η y) ∧
    (unitOT a b c η y).B w - (unitOT a b c η y).d =
      otBeta b η * (otUpper a η y - w) ^ 2 := by
  have hd : 0 < 4 - η ^ 2 := by nlinarith
  have hc' : InCHat a η y w := ⟨hc.2, hc.1⟩
  constructor
  · change supplierOT a b c η w y - disagreeOT a b c η y = _
    rw [disagreeOT_formula hb hη0 hη1 hya]
    unfold supplierOT ROT
    rw [qOT_closed_general hb hη0 hη1 hc, qOT_closed_general hb hη0 hη1 hc']
    unfold otAlpha otUpper otLower
    field_simp
    ring
  · change retailerOT a b η w y - 0 = _
    unfold retailerOT rOT priceOT price
    rw [qOT_closed_general hb hη0 hη1 hc, qOT_closed_general hb hη0 hη1 hc']
    unfold otBeta otUpper
    field_simp
    ring

theorem to_surpluses_closed {a b c η w y : ℝ} (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hya : y ≤ a) (hc : InCCheck a η w y) :
    (unitTO a b c η y).S w - (unitTO a b c η y).D =
      toAlpha b η * (toUpper a η y - w) * (w - c) ∧
    (unitTO a b c η y).B w - (unitTO a b c η y).d =
      toBeta b η * (toUpper a η y - w) ^ 2 := by
  have hd : 0 < 1 - η ^ 2 := by nlinarith
  have hc' : InCCheck a η y w := ⟨hc.2, hc.1⟩
  constructor
  · change supplierTO a b c η w y - 0 = _
    unfold supplierTO RTO
    rw [qTO_closed_general hb hη0 hη1 hc]
    unfold toAlpha toUpper
    ring
  · change retailerTO a b η w y - disagreeTO a b η y = _
    rw [disagreeTO_formula hb hη0 hη1 hya]
    unfold retailerTO rTO priceTO price
    rw [qTO_closed_general hb hη0 hη1 hc, qTO_closed_general hb hη0 hη1 hc']
    unfold toBeta toUpper
    field_simp
    ring

theorem ot_zero_quantities {a b η w y : ℝ} (_hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hwa : w ≤ a) (hya : y ≤ a) (hwH : otUpper a η y < w) :
    qOT a b η w y = 0 ∧ qOT a b η y w = (a - y) / (2 * b) := by
  have hx := mul_le_of_le_one_left (sub_nonneg.mpr hwa) hη1
  have hy := mul_le_of_le_one_left (sub_nonneg.mpr hya) hη1
  have hfirst : 2 * (a - w) ≤ η * (a - y) := by dsimp [otUpper] at hwH; linarith
  have hother : ¬ 2 * (a - y) ≤ η * (a - w) := by
    dsimp [otUpper] at hwH
    intro hn
    nlinarith
  constructor
  · simp only [qOT, if_pos hfirst]
  · simp only [qOT, if_neg hother, if_pos hfirst]

theorem to_zero_quantities {a b η w y : ℝ} (_hη0 : 0 ≤ η) (hη1 : η < 1)
    (hwa : w ≤ a) (hya : y ≤ a) (hwH : toUpper a η y < w) :
    qTO a b η w y = 0 ∧ qTO a b η y w = (a - y) / (2 * b) := by
  have hx := mul_le_of_le_one_left (sub_nonneg.mpr hwa) hη1.le
  have hy := mul_le_of_le_one_left (sub_nonneg.mpr hya) hη1.le
  have hfirst : a - w ≤ η * (a - y) := by dsimp [toUpper] at hwH; linarith
  have hother : ¬ a - y ≤ η * (a - w) := by
    dsimp [toUpper] at hwH
    intro hn
    linarith
  constructor
  · simp only [qTO, if_pos hfirst]
  · simp only [qTO, if_neg hother, if_pos hfirst]

theorem ot_surpluses_zero {a b c η w y : ℝ} (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hwa : w ≤ a) (hya : y ≤ a)
    (hwH : otUpper a η y < w) :
    (unitOT a b c η y).S w - (unitOT a b c η y).D = 0 ∧
    (unitOT a b c η y).B w - (unitOT a b c η y).d = 0 := by
  obtain ⟨hq, hq'⟩ := ot_zero_quantities (b := b) hη0 hη1 hwa hya hwH
  constructor
  · change supplierOT a b c η w y - disagreeOT a b c η y = 0
    rw [disagreeOT_formula hb hη0 hη1 hya]
    unfold supplierOT ROT
    rw [hq, hq']
    ring
  · change retailerOT a b η w y - 0 = 0
    simp [retailerOT, rOT, hq]

theorem to_surpluses_zero {a b c η w y : ℝ} (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hwa : w ≤ a) (hya : y ≤ a)
    (hwH : toUpper a η y < w) :
    (unitTO a b c η y).S w - (unitTO a b c η y).D = 0 ∧
    (unitTO a b c η y).B w - (unitTO a b c η y).d = 0 := by
  obtain ⟨hq, hq'⟩ := to_zero_quantities (b := b) hη0 hη1 hwa hya hwH
  constructor
  · change supplierTO a b c η w y - 0 = 0
    simp [supplierTO, RTO, hq]
  · change retailerTO a b η w y - disagreeTO a b η y = 0
    rw [disagreeTO_formula hb hη0 hη1 hya]
    unfold retailerTO rTO priceTO price
    rw [hq, hq']
    field_simp
    ring

theorem unitOT_shape {a b c η y : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hcy : c ≤ y) (hy : y ≤ c + (a - c) / 2) :
    Shape (unitOT a b c η y) (otLower c η y) (otUpper a η y)
      (otAlpha b η) (otBeta b η) := by
  have hya : y ≤ a := by linarith
  have hd : 0 < 4 - η ^ 2 := by nlinarith
  have hL : c ≤ otLower c η y := by
    dsimp [otLower]
    nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hcy)]
  have hH : otUpper a η y ≤ a := by
    dsimp [otUpper]
    nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hya)]
  have hLH : otLower c η y < otUpper a η y := by
    dsimp [otLower, otUpper]
    nlinarith [mul_nonneg (sub_nonneg.mpr hη1) (sub_nonneg.mpr hac.le)]
  have hc (w : ℝ) (hw : w ∈ (unitOT a b c η y).W) (hwH : w ≤ otUpper a η y) :
      InCHat a η w y := by
    change c ≤ w ∧ w ≤ a at hw
    constructor
    · dsimp [otUpper] at hwH
      linarith
    · have he := mul_le_of_le_one_left (sub_nonneg.mpr hw.2) hη1
      linarith
  refine ⟨hLH, ?_, ?_, ?_, ?_, ?_⟩
  · unfold otAlpha
    positivity
  · unfold otBeta
    positivity
  · intro w hwL hwH
    exact ⟨hL.trans hwL, hwH.trans hH⟩
  · intro w hw
    by_cases hwH : w ≤ otUpper a η y
    · rw [if_pos hwH]
      exact (ot_surpluses_closed hb hη0 hη1 hya (hc w hw hwH)).1
    · rw [if_neg hwH]
      exact (ot_surpluses_zero hb hη0 hη1 hw.2 hya (lt_of_not_ge hwH)).1
  · intro w hw
    by_cases hwH : w ≤ otUpper a η y
    · rw [if_pos hwH]
      exact (ot_surpluses_closed hb hη0 hη1 hya (hc w hw hwH)).2
    · rw [if_neg hwH]
      exact (ot_surpluses_zero hb hη0 hη1 hw.2 hya (lt_of_not_ge hwH)).2

theorem unitTO_shape {a b c η y : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hcy : c ≤ y) (hy : y ≤ c + (1 - η) * (a - c)) :
    Shape (unitTO a b c η y) c (toUpper a η y) (toAlpha b η) (toBeta b η) := by
  have hya : y ≤ a := by nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hac.le)]
  have hd : 0 < 1 - η ^ 2 := by nlinarith
  have hH : toUpper a η y ≤ a := by
    dsimp [toUpper]
    nlinarith [mul_nonneg hη0 (sub_nonneg.mpr hya)]
  have hLH : c < toUpper a η y := by
    dsimp [toUpper]
    nlinarith [mul_pos (sub_pos.mpr hη1) (sub_pos.mpr hac),
      mul_nonneg hη0 (sub_nonneg.mpr hcy)]
  have hc (w : ℝ) (hw : w ∈ (unitTO a b c η y).W) (hwH : w ≤ toUpper a η y) :
      InCCheck a η w y := by
    change c ≤ w ∧ w ≤ a at hw
    constructor
    · dsimp [toUpper] at hwH
      linarith
    · have he := mul_le_mul_of_nonneg_left (sub_le_sub_left hw.1 a) hη0
      nlinarith
  refine ⟨hLH, ?_, ?_, ?_, ?_, ?_⟩
  · unfold toAlpha
    positivity
  · unfold toBeta
    positivity
  · intro w hwL hwH
    exact ⟨hwL, hwH.trans hH⟩
  · intro w hw
    by_cases hwH : w ≤ toUpper a η y
    · rw [if_pos hwH]
      exact (to_surpluses_closed hb hη0 hη1 hya (hc w hw hwH)).1
    · rw [if_neg hwH]
      exact (to_surpluses_zero hb hη0 hη1 hw.2 hya (lt_of_not_ge hwH)).1
  · intro w hw
    by_cases hwH : w ≤ toUpper a η y
    · rw [if_pos hwH]
      exact (to_surpluses_closed hb hη0 hη1 hya (hc w hw hwH)).2
    · rw [if_neg hwH]
      exact (to_surpluses_zero hb hη0 hη1 hw.2 hya (lt_of_not_ge hwH)).2

end S11CanonicalUnits
end


set_option autoImplicit false
noncomputable section

namespace S11Nash

def canonicalProduct (θ α β x : ℝ) : ℝ :=
  (β * (1 - x) ^ 2) ^ θ * (α * x * (1 - x)) ^ (1 - θ)

theorem polynomial_maximum (x : ℝ) (hx : x ≤ 1) :
    x * (1 - x) ^ 4 ≤ (1 / 5 : ℝ) * (1 - 1 / 5) ^ 4 := by
  have hC : 0 < 16 + 40 * (1 - x) + 75 * (1 - x) ^ 2 + 125 * (1 - x) ^ 3 := by
    have hy : 0 ≤ 1 - x := sub_nonneg.mpr hx
    positivity
  have hc : 256 - 3125 * (x * (1 - x) ^ 4) =
      (5 * x - 1) ^ 2 *
        (16 + 40 * (1 - x) + 75 * (1 - x) ^ 2 + 125 * (1 - x) ^ 3) := by ring
  have hp := mul_nonneg (sq_nonneg (5 * x - 1)) hC.le
  norm_num
  nlinarith

theorem polynomial_strict_maximum (x : ℝ) (hx : x ≤ 1) (hne : x ≠ 1 / 5) :
    x * (1 - x) ^ 4 < (1 / 5 : ℝ) * (1 - 1 / 5) ^ 4 := by
  have hC : 0 < 16 + 40 * (1 - x) + 75 * (1 - x) ^ 2 + 125 * (1 - x) ^ 3 := by
    have hy : 0 ≤ 1 - x := sub_nonneg.mpr hx
    positivity
  have hc : 256 - 3125 * (x * (1 - x) ^ 4) =
      (5 * x - 1) ^ 2 *
        (16 + 40 * (1 - x) + 75 * (1 - x) ^ 2 + 125 * (1 - x) ^ 3) := by ring
  have hz : 5 * x - 1 ≠ 0 := by intro he; apply hne; linarith
  have hp := mul_pos (sq_pos_of_ne_zero hz) hC
  norm_num
  nlinarith

theorem canonicalProduct_nonneg (θ α β x : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ canonicalProduct θ α β x := by
  unfold canonicalProduct
  have hy : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

theorem canonicalProduct_three_fifths_pow (α β x : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    canonicalProduct (3 / 5) α β x ^ 5 =
      (α ^ 2 * β ^ 3) * (x * (1 - x) ^ 4) ^ 2 := by
  have hS : 0 ≤ α * x * (1 - x) := mul_nonneg (mul_nonneg hα hx0) (sub_nonneg.mpr hx1)
  have hB : 0 ≤ β * (1 - x) ^ 2 := mul_nonneg hβ (sq_nonneg _)
  unfold canonicalProduct
  rw [mul_pow, ← Real.rpow_mul_natCast hB, ← Real.rpow_mul_natCast hS]
  norm_num
  ring

theorem canonicalProduct_three_fifths_le (α β x : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    canonicalProduct (3 / 5) α β x ≤ canonicalProduct (3 / 5) α β (1 / 5) := by
  apply (pow_le_pow_iff_left₀
    (canonicalProduct_nonneg _ _ _ _ hα hβ hx0 hx1)
    (canonicalProduct_nonneg _ _ _ _ hα hβ (by norm_num) (by norm_num))
    (by decide : (5 : ℕ) ≠ 0)).mp
  rw [canonicalProduct_three_fifths_pow α β x hα hβ hx0 hx1,
    canonicalProduct_three_fifths_pow α β (1 / 5) hα hβ (by norm_num) (by norm_num)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (polynomial_maximum x hx1) 2

theorem canonicalProduct_three_fifths_lt (α β x : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hne : x ≠ 1 / 5) :
    canonicalProduct (3 / 5) α β x < canonicalProduct (3 / 5) α β (1 / 5) := by
  apply (pow_lt_pow_iff_left₀
    (canonicalProduct_nonneg _ _ _ _ hα.le hβ.le hx0 hx1)
    (canonicalProduct_nonneg _ _ _ _ hα.le hβ.le (by norm_num) (by norm_num))
    (by decide : (5 : ℕ) ≠ 0)).mp
  rw [canonicalProduct_three_fifths_pow α β x hα.le hβ.le hx0 hx1,
    canonicalProduct_three_fifths_pow α β (1 / 5) hα.le hβ.le (by norm_num) (by norm_num)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact (pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by decide : (2 : ℕ) ≠ 0)).mpr
    (polynomial_strict_maximum x hx1 hne)

def logarithmicScore (θ α β x : ℝ) : ℝ :=
  θ * Real.log (β * (1 - x) ^ 2) +
    (1 - θ) * Real.log (α * x * (1 - x))

theorem log_canonicalProduct (θ α β x : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (canonicalProduct θ α β x) = logarithmicScore θ α β x := by
  have hS : 0 < α * x * (1 - x) := mul_pos (mul_pos hα hx0) (sub_pos.mpr hx1)
  have hB : 0 < β * (1 - x) ^ 2 := mul_pos hβ (sq_pos_of_pos (sub_pos.mpr hx1))
  rw [canonicalProduct, Real.log_mul (Real.rpow_pos_of_pos hB _).ne'
    (Real.rpow_pos_of_pos hS _).ne', Real.log_rpow hB, Real.log_rpow hS]
  rfl

theorem logarithmicScore_hasDerivAt (θ α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    HasDerivAt (logarithmicScore θ α β) ((15 - 25 * θ) / 4) (1 / 5) := by
  have hB := (((hasDerivAt_id (1 / 5 : ℝ)).const_sub 1).pow 2).const_mul β
  have hS := ((hasDerivAt_id (1 / 5 : ℝ)).const_mul α).mul
    ((hasDerivAt_id (1 / 5 : ℝ)).const_sub 1)
  have hBn : β * (1 - (1 / 5 : ℝ)) ^ 2 ≠ 0 := by positivity
  have hSn : α * (1 / 5 : ℝ) * (1 - 1 / 5) ≠ 0 := by positivity
  have hh := ((hB.log hBn).const_mul θ).add ((hS.log hSn).const_mul (1 - θ))
  unfold logarithmicScore
  exact hh.congr_deriv (by dsimp; field_simp [hα.ne', hβ.ne']; ring)

theorem power_for_one_fifth (θ α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hmax : ∀ x : ℝ, 0 < x → x < 1 →
      canonicalProduct θ α β x ≤ canonicalProduct θ α β (1 / 5)) :
    θ = 3 / 5 := by
  have hs : IsMaxOn (logarithmicScore θ α β) (Set.Ioo 0 1) (1 / 5) := by
    intro x hx
    change logarithmicScore θ α β x ≤ logarithmicScore θ α β (1 / 5)
    rw [← log_canonicalProduct θ α β x hα hβ hx.1 hx.2,
      ← log_canonicalProduct θ α β (1 / 5) hα hβ (by norm_num) (by norm_num)]
    have hp : 0 < canonicalProduct θ α β x := by
      unfold canonicalProduct
      have hy : 0 < 1 - x := sub_pos.mpr hx.2
      exact mul_pos (Real.rpow_pos_of_pos (mul_pos hβ (sq_pos_of_pos hy)) _)
        (Real.rpow_pos_of_pos (mul_pos (mul_pos hα hx.1) hy) _)
    exact Real.log_le_log hp (hmax x hx.1 hx.2)
  have hl : IsLocalMax (logarithmicScore θ α β) (1 / 5) :=
    hs.isLocalMax (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hz := hl.hasDerivAt_eq_zero (logarithmicScore_hasDerivAt θ α β hα hβ)
  linarith

end S11Nash
end



set_option autoImplicit false
noncomputable section
open CompetingKS

namespace S11NashPareto

theorem nb_no_strict_dominator (U : BargainingUnit) (θ w : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : U.IsNBResponse θ w) :
    ¬ ∃ z ∈ U.W, U.S w < U.S z ∧ U.B w < U.B z := by
  rintro ⟨z, hz, hS, hB⟩
  have hirz : U.IsIR z := ⟨hz, hr.1.2.1.trans hS.le, hr.1.2.2.trans hB.le⟩
  have hSp : 0 ≤ U.S w - U.D := sub_nonneg.mpr hr.1.2.1
  have hBp : 0 ≤ U.B w - U.d := sub_nonneg.mpr hr.1.2.2
  have hS' : U.S w - U.D < U.S z - U.D := sub_lt_sub_right hS _
  have hB' : U.B w - U.d < U.B z - U.d := sub_lt_sub_right hB _
  have hBpz : 0 < U.B z - U.d := hBp.trans_lt hB'
  have hlt : U.nashProduct θ w < U.nashProduct θ z := by
    unfold BargainingUnit.nashProduct
    calc
      _ ≤ (U.B z - U.d) ^ θ * (U.S w - U.D) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hBp hB'.le hθ0.le)
          (Real.rpow_nonneg hSp _)
      _ < _ := mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow hSp hS' (sub_pos.mpr hθ1))
        (Real.rpow_pos_of_pos hBpz _)
  exact (not_lt_of_ge (hr.2 z hirz)) hlt

theorem response_product_pos_of_benchmark (U : BargainingUnit) (θ w z : ℝ)
    (hr : U.IsNBResponse θ w) (hz : U.IsIR z)
    (hS : 0 < U.S z - U.D) (hB : 0 < U.B z - U.d) :
    0 < U.nashProduct θ w := by
  have hp : 0 < U.nashProduct θ z := by
    exact mul_pos (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hS _)
  exact hp.trans_le (hr.2 z hz)

theorem response_surpluses_pos (U : BargainingUnit) (θ w : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : U.IsNBResponse θ w)
    (hp : 0 < U.nashProduct θ w) :
    0 < U.S w - U.D ∧ 0 < U.B w - U.d := by
  constructor
  · by_contra hn
    have hz : U.S w - U.D = 0 :=
      le_antisymm (le_of_not_gt hn) (sub_nonneg.mpr hr.1.2.1)
    have he : U.nashProduct θ w = 0 := by
      rw [BargainingUnit.nashProduct, hz, Real.zero_rpow (sub_pos.mpr hθ1).ne', mul_zero]
    linarith
  · by_contra hn
    have hz : U.B w - U.d = 0 :=
      le_antisymm (le_of_not_gt hn) (sub_nonneg.mpr hr.1.2.2)
    have he : U.nashProduct θ w = 0 := by
      rw [BargainingUnit.nashProduct, hz, Real.zero_rpow hθ0.ne', zero_mul]
    linarith

theorem pareto_of_nb_positive (U : BargainingUnit) (θ w : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : U.IsNBResponse θ w)
    (hp : 0 < U.nashProduct θ w) : U.IsPareto w := by
  refine ⟨hr.1.1, ?_⟩
  rintro ⟨z, hz, hS, hB, hstrict⟩
  have hirz : U.IsIR z := ⟨hz, hr.1.2.1.trans hS, hr.1.2.2.trans hB⟩
  obtain ⟨hSp, hBp⟩ := response_surpluses_pos U θ w hθ0 hθ1 hr hp
  have hS' : U.S w - U.D ≤ U.S z - U.D := sub_le_sub_right hS _
  have hB' : U.B w - U.d ≤ U.B z - U.d := sub_le_sub_right hB _
  have hSpz : 0 < U.S z - U.D := hSp.trans_le hS'
  have hBpz : 0 < U.B z - U.d := hBp.trans_le hB'
  have hlt : U.nashProduct θ w < U.nashProduct θ z := by
    unfold BargainingUnit.nashProduct
    rcases hstrict with hs | hb
    · calc
        _ < (U.B w - U.d) ^ θ * (U.S z - U.D) ^ (1 - θ) :=
          mul_lt_mul_of_pos_left
            (Real.rpow_lt_rpow hSp.le (sub_lt_sub_right hs _) (sub_pos.mpr hθ1))
            (Real.rpow_pos_of_pos hBp _)
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hBp.le hB' hθ0.le) (Real.rpow_nonneg hSpz.le _)
    · calc
        _ < (U.B z - U.d) ^ θ * (U.S w - U.D) ^ (1 - θ) :=
          mul_lt_mul_of_pos_right
            (Real.rpow_lt_rpow hBp.le (sub_lt_sub_right hb _) hθ0)
            (Real.rpow_pos_of_pos hSp _)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hSp.le hS' (sub_pos.mpr hθ1).le) (Real.rpow_nonneg hBpz.le _)
  exact (not_lt_of_ge (hr.2 z hirz)) hlt

end S11NashPareto
end



set_option autoImplicit false
noncomputable section
open CompetingKS S11Nash S11NashPareto

namespace S11CanonicalKS

variable {U : BargainingUnit} {ℓ H α β : ℝ} (h : Shape U ℓ H α β)
include h

theorem Shape.product_eq (θ w : ℝ) (hw : w ∈ U.W) (hwH : w ≤ H) :
    U.nashProduct θ w = canonicalProduct θ (α * (H - ℓ) ^ 2)
      (β * (H - ℓ) ^ 2) ((w - ℓ) / (H - ℓ)) := by
  have hn : H - ℓ ≠ 0 := (sub_pos.mpr h.interval_pos).ne'
  have hs : α * (H - w) * (w - ℓ) =
      (α * (H - ℓ) ^ 2) * ((w - ℓ) / (H - ℓ)) * (1 - (w - ℓ) / (H - ℓ)) := by
    field_simp [hn]
    <;> ring
  have hb : β * (H - w) ^ 2 =
      (β * (H - ℓ) ^ 2) * (1 - (w - ℓ) / (H - ℓ)) ^ 2 := by
    field_simp [hn]
    <;> ring
  rw [BargainingUnit.nashProduct, h.seller w hw, h.buyer w hw, if_pos hwH, if_pos hwH, hs, hb]
  rfl

theorem Shape.product_ksPrice (θ : ℝ) :
    U.nashProduct θ (ksPrice ℓ H) =
      canonicalProduct θ (α * (H - ℓ) ^ 2) (β * (H - ℓ) ^ 2) (1 / 5) := by
  rw [h.product_eq θ _ h.ksPrice_mem (by unfold ksPrice; linarith [h.interval_pos])]
  have hx : (ksPrice ℓ H - ℓ) / (H - ℓ) = 1 / 5 := by
    unfold ksPrice
    field_simp [(sub_pos.mpr h.interval_pos).ne']
    <;> ring
  rw [hx]

theorem Shape.ksPrice_ir : U.IsIR (ksPrice ℓ H) :=
  (h.ir_iff _).mpr ⟨h.ksPrice_mem, by unfold ksPrice; linarith [h.interval_pos]⟩

theorem Shape.ksPrice_product_pos (θ : ℝ) : 0 < U.nashProduct θ (ksPrice ℓ H) := by
  obtain ⟨hs, hb⟩ := h.ksPrice_surplus_pos
  exact mul_pos (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos hs _)

theorem Shape.nb_three_fifths_iff (w : ℝ) :
    U.IsNBResponse (3 / 5) w ↔ w = ksPrice ℓ H := by
  have hK : 0 < H - ℓ := sub_pos.mpr h.interval_pos
  have hα : 0 < α * (H - ℓ) ^ 2 := mul_pos h.seller_scale_pos (sq_pos_of_pos hK)
  have hβ : 0 < β * (H - ℓ) ^ 2 := mul_pos h.buyer_scale_pos (sq_pos_of_pos hK)
  constructor
  · intro hr
    have hp : 0 < U.nashProduct (3 / 5) w :=
      (h.ksPrice_product_pos _).trans_le (hr.2 _ h.ksPrice_ir)
    have hwℓ : ℓ ≤ w := ((h.ir_iff w).mp hr.1).2
    have hwH : w < H := by
      by_contra hn
      obtain ⟨_, hb⟩ := h.surpluses_zero_of_ge w hr.1.1 (le_of_not_gt hn)
      have hz : U.nashProduct (3 / 5) w = 0 := by
        rw [BargainingUnit.nashProduct, hb, Real.zero_rpow (by norm_num : (3 / 5 : ℝ) ≠ 0),
          zero_mul]
      linarith
    by_contra hne
    have hxn : (w - ℓ) / (H - ℓ) ≠ 1 / 5 := by
      intro he
      have he' := (div_eq_iff hK.ne').mp he
      apply hne
      unfold ksPrice
      linarith
    have hlt : U.nashProduct (3 / 5) w < U.nashProduct (3 / 5) (ksPrice ℓ H) := by
      rw [h.product_eq _ w hr.1.1 hwH.le, h.product_ksPrice]
      exact canonicalProduct_three_fifths_lt _ _ _ hα hβ
        (div_nonneg (sub_nonneg.mpr hwℓ) hK.le)
        ((div_le_one hK).mpr (by linarith)) hxn
    exact (not_lt_of_ge (hr.2 _ h.ksPrice_ir)) hlt
  · rintro rfl
    refine ⟨h.ksPrice_ir, ?_⟩
    intro w hw
    have hwℓ : ℓ ≤ w := ((h.ir_iff w).mp hw).2
    by_cases hwH : w ≤ H
    · rw [h.product_eq _ w hw.1 hwH, h.product_ksPrice]
      exact canonicalProduct_three_fifths_le _ _ _ hα.le hβ.le
        (div_nonneg (sub_nonneg.mpr hwℓ) hK.le)
        ((div_le_one hK).mpr (by linarith))
    · obtain ⟨_, hb⟩ := h.surpluses_zero_of_ge w hw.1 (le_of_lt (lt_of_not_ge hwH))
      have hz : U.nashProduct (3 / 5) w = 0 := by
        rw [BargainingUnit.nashProduct, hb, Real.zero_rpow (by norm_num : (3 / 5 : ℝ) ≠ 0),
          zero_mul]
      rw [hz]
      exact (h.ksPrice_product_pos _).le

theorem Shape.nb_ksPrice_iff (θ : ℝ) :
    U.IsNBResponse θ (ksPrice ℓ H) ↔ θ = 3 / 5 := by
  have hK : 0 < H - ℓ := sub_pos.mpr h.interval_pos
  have hα : 0 < α * (H - ℓ) ^ 2 := mul_pos h.seller_scale_pos (sq_pos_of_pos hK)
  have hβ : 0 < β * (H - ℓ) ^ 2 := mul_pos h.buyer_scale_pos (sq_pos_of_pos hK)
  constructor
  · intro hr
    apply power_for_one_fifth θ _ _ hα hβ
    intro x hx0 hx1
    let w := ℓ + (H - ℓ) * x
    have hwℓ : ℓ ≤ w := by dsimp [w]; nlinarith
    have hwH : w ≤ H := by dsimp [w]; nlinarith
    have hw : w ∈ U.W := h.interval_mem w hwℓ hwH
    have hir : U.IsIR w := (h.ir_iff w).mpr ⟨hw, hwℓ⟩
    have he : (w - ℓ) / (H - ℓ) = x := by dsimp [w]; field_simp [hK.ne']; ring
    have hm := hr.2 w hir
    rw [h.product_eq θ w hw hwH, h.product_ksPrice, he] at hm
    exact hm
  · rintro rfl
    exact (h.nb_three_fifths_iff _).mpr rfl

end S11CanonicalKS
end



set_option autoImplicit false
noncomputable section
open CompetingKS S11CanonicalKS S11CanonicalUnits S11Pareto

namespace S11KSEquilibria

theorem ksOT_candidate {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    IsKSEqOT 1 1 0 η (1 / 5) (1 / 5) := by
  have hs := unitOT_shape (a := 1) (b := 1) (c := 0) (y := 1 / 5)
    (by norm_num) (by norm_num) hη0 hη1 (by norm_num) (by norm_num)
  have hr : (normOT η (1 / 5)).IsKSResponse (1 / 5) :=
    (hs.ks_iff _).mpr (by unfold ksPrice otLower otUpper; ring)
  refine ⟨?_, hr, hr⟩
  constructor <;> norm_num <;> nlinarith

theorem ksTO_candidate {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    IsKSEqTO 1 1 0 η ((1 - η) / (5 - η)) ((1 - η) / (5 - η)) := by
  have hd : 0 < 5 - η := by linarith
  have hq0 : 0 ≤ (1 - η) / (5 - η) := div_nonneg (by linarith) hd.le
  have hql : (1 - η) / (5 - η) ≤ 1 - η := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1 - η by linarith) (show 0 ≤ 4 - η by linarith)]
  have hq1 : (1 - η) / (5 - η) ≤ 1 := hql.trans (by linarith)
  have hs := unitTO_shape (a := 1) (b := 1) (c := 0) (y := (1 - η) / (5 - η))
    (by norm_num) (by norm_num) hη0 hη1 hq0 (by simpa using hql)
  have hr : (normTO η ((1 - η) / (5 - η))).IsKSResponse ((1 - η) / (5 - η)) :=
    (hs.ks_iff _).mpr (by unfold ksPrice toUpper; field_simp; ring)
  have hi : InCCheck 1 η ((1 - η) / (5 - η)) ((1 - η) / (5 - η)) := by
    have hm := mul_le_of_le_one_left (sub_nonneg.mpr hq1) hη1.le
    exact ⟨hm, hm⟩
  exact ⟨hi, hr, hr⟩

theorem ksOT_unique_of_low {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (he : IsKSEqOT 1 1 0 η x y) (hxl : x ≤ 1 / 2) (hyl : y ≤ 1 / 2) :
    x = 1 / 5 ∧ y = 1 / 5 := by
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := he.2.1.1.1
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := he.2.2.1.1
  have hsx := unitOT_shape (a := 1) (b := 1) (c := 0) (y := y)
    (by norm_num) (by norm_num) hη0 hη1 hy.1 (by simpa using hyl)
  have hsy := unitOT_shape (a := 1) (b := 1) (c := 0) (y := x)
    (by norm_num) (by norm_num) hη0 hη1 hx.1 (by simpa using hxl)
  have he1 := (hsx.ks_iff x).mp he.2.1
  have he2 := (hsy.ks_iff y).mp he.2.2
  dsimp [ksPrice, otLower, otUpper] at he1 he2
  have hdiff : (2 + η) * (x - y) = 0 := by nlinarith
  have hxy : x = y := sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff).resolve_left (ne_of_gt (by linarith)))
  rw [← hxy] at he1 ⊢
  have hxprod : (2 - η) * (x - 1 / 5) = 0 := by nlinarith
  have hxval : x = 1 / 5 := sub_eq_zero.mp
    ((mul_eq_zero.mp hxprod).resolve_left (ne_of_gt (by linarith)))
  exact ⟨hxval, hxval⟩

theorem ksTO_unique_of_low {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (he : IsKSEqTO 1 1 0 η x y) (hxl : x ≤ 1 - η) (hyl : y ≤ 1 - η) :
    x = (1 - η) / (5 - η) ∧ y = (1 - η) / (5 - η) := by
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := he.2.1.1.1
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := he.2.2.1.1
  have hsx := unitTO_shape (a := 1) (b := 1) (c := 0) (y := y)
    (by norm_num) (by norm_num) hη0 hη1 hy.1 (by simpa using hyl)
  have hsy := unitTO_shape (a := 1) (b := 1) (c := 0) (y := x)
    (by norm_num) (by norm_num) hη0 hη1 hx.1 (by simpa using hxl)
  have he1 := (hsx.ks_iff x).mp he.2.1
  have he2 := (hsy.ks_iff y).mp he.2.2
  dsimp [ksPrice, toUpper] at he1 he2
  have hdiff : (5 + η) * (x - y) = 0 := by nlinarith
  have hxy : x = y := sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff).resolve_left (ne_of_gt (by linarith)))
  rw [← hxy] at he1 ⊢
  have hxval : x = (1 - η) / (5 - η) := by
    apply (eq_div_iff (by linarith : 5 - η ≠ 0)).mpr
    nlinarith
  exact ⟨hxval, hxval⟩

theorem ksOT_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    IsKSEqOT 1 1 0 η x y ↔ x = 1 / 5 ∧ y = 1 / 5 := by
  constructor
  · intro he
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := he.2.1.1.1
    have hy : y ∈ Set.Icc (0 : ℝ) 1 := he.2.2.1.1
    have hl : x ≤ 1 / 2 ∧ y ≤ 1 / 2 := by
      rcases le_total x y with hxy | hyx
      · have hb := ot_pareto_max_le_half hη0 hη1 hx hxy
          (show InCHat 1 η y x from ⟨he.1.2, he.1.1⟩) he.2.2.2.1
        exact ⟨hxy.trans hb, hb⟩
      · have hb := ot_pareto_max_le_half hη0 hη1 hy hyx he.1 he.2.1.2.1
        exact ⟨hb, hyx.trans hb⟩
    exact ksOT_unique_of_low hη0 hη1 he hl.1 hl.2
  · rintro ⟨rfl, rfl⟩
    exact ksOT_candidate hη0 hη1

theorem ksTO_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    IsKSEqTO 1 1 0 η x y ↔
      x = (1 - η) / (5 - η) ∧ y = (1 - η) / (5 - η) := by
  constructor
  · intro he
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := he.2.1.1.1
    have hy : y ∈ Set.Icc (0 : ℝ) 1 := he.2.2.1.1
    have hsmall : (1 - η) / (2 - η) ≤ 1 - η := by
      apply (div_le_iff₀ (by linarith : 0 < 2 - η)).mpr
      nlinarith [sq_nonneg (1 - η)]
    have hl : x ≤ 1 - η ∧ y ≤ 1 - η := by
      rcases le_total x y with hxy | hyx
      · have hb := (to_pareto_max_le hη0 hη1 hx hxy
          (show InCCheck 1 η y x from ⟨he.1.2, he.1.1⟩) he.2.2.2.1).trans hsmall
        exact ⟨hxy.trans hb, hb⟩
      · have hb := (to_pareto_max_le hη0 hη1 hy hyx he.1 he.2.1.2.1).trans hsmall
        exact ⟨hb, hyx.trans hb⟩
    exact ksTO_unique_of_low hη0 hη1 he hl.1 hl.2
  · rintro ⟨rfl, rfl⟩
    exact ksTO_candidate hη0 hη1

end S11KSEquilibria
end


set_option autoImplicit false
noncomputable section
open CompetingKS S11CanonicalKS S11CanonicalUnits S11NashPareto S11Pareto

namespace S11NBEquilibria

theorem nbOT_at_point_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (θ : ℝ) :
    IsNBEqOT 1 1 0 η θ (1 / 5) (1 / 5) ↔ θ = 3 / 5 := by
  have hs := unitOT_shape (a := 1) (b := 1) (c := 0) (y := 1 / 5)
    (by norm_num) (by norm_num) hη0 hη1 (by norm_num) (by norm_num)
  have he : ksPrice (otLower 0 η (1 / 5)) (otUpper 1 η (1 / 5)) = (1 / 5 : ℝ) := by
    unfold ksPrice otLower otUpper
    ring
  constructor
  · intro hr
    apply (hs.nb_ksPrice_iff θ).mp
    rw [he]
    exact hr.2.1
  · rintro rfl
    have hn : (normOT η (1 / 5)).IsNBResponse (3 / 5) (1 / 5) := by
      apply (hs.nb_three_fifths_iff _).mpr
      exact he.symm
    refine ⟨?_, hn, hn⟩
    constructor <;> nlinarith

theorem nbTO_at_point_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (θ : ℝ) :
    IsNBEqTO 1 1 0 η θ ((1 - η) / (5 - η)) ((1 - η) / (5 - η)) ↔ θ = 3 / 5 := by
  let p := (1 - η) / (5 - η)
  have hd : 0 < 5 - η := by linarith
  have hp0 : 0 ≤ p := div_nonneg (sub_pos.mpr hη1).le hd.le
  have hpL : p ≤ 1 - η := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (1 - η)]
  have hp1 : p ≤ 1 := by linarith
  have hs := unitTO_shape (a := 1) (b := 1) (c := 0) (y := p)
    (by norm_num) (by norm_num) hη0 hη1 hp0 (by simpa using hpL)
  have hpE : p * (5 - η) = 1 - η := by dsimp [p]; field_simp
  have he : ksPrice 0 (toUpper 1 η p) = p := by
    unfold ksPrice toUpper
    nlinarith only [hpE]
  change IsNBEqTO 1 1 0 η θ p p ↔ θ = 3 / 5
  constructor
  · intro hr
    apply (hs.nb_ksPrice_iff θ).mp
    rw [he]
    exact hr.2.1
  · rintro rfl
    have hn : (normTO η p).IsNBResponse (3 / 5) p := by
      apply (hs.nb_three_fifths_iff _).mpr
      exact he.symm
    refine ⟨?_, hn, hn⟩
    constructor <;> exact mul_le_of_le_one_left (sub_nonneg.mpr hp1) hη1.le

theorem nbOT_bounds {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hr : IsNBEqOT 1 1 0 η (3 / 5) x y) : x ≤ 1 / 2 ∧ y ≤ 1 / 2 := by
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := hr.2.1.1.1
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := hr.2.2.1.1
  rcases le_total y x with hxy | hyx
  · have hbound : x ≤ 1 / 2 := by
      by_contra hn
      have hc := ot_strict_dominator_of_large_max hη0 hη1 hx.1 hx.2 hy.1 hy.2
        hxy hr.1 (lt_of_not_ge hn)
      exact nb_no_strict_dominator (normOT η y) (3 / 5) x
        (by norm_num) (by norm_num) hr.2.1 hc
    exact ⟨hbound, hxy.trans hbound⟩
  · have hbound : y ≤ 1 / 2 := by
      by_contra hn
      have hc := ot_strict_dominator_of_large_max hη0 hη1 hy.1 hy.2 hx.1 hx.2
        hyx ⟨hr.1.2, hr.1.1⟩ (lt_of_not_ge hn)
      exact nb_no_strict_dominator (normOT η x) (3 / 5) y
        (by norm_num) (by norm_num) hr.2.2 hc
    exact ⟨hyx.trans hbound, hbound⟩

theorem nbTO_bounds {η x y : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hr : IsNBEqTO 1 1 0 η (3 / 5) x y) :
    x ≤ (1 - η) / (2 - η) ∧ y ≤ (1 - η) / (2 - η) := by
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := hr.2.1.1.1
  have hy : y ∈ Set.Icc (0 : ℝ) 1 := hr.2.2.1.1
  rcases le_total y x with hxy | hyx
  · have hbound : x ≤ (1 - η) / (2 - η) := by
      by_contra hn
      have hc := to_strict_dominator_of_large_max hη0 hη1 hx.1 hx.2 hy.1 hy.2
        hxy hr.1 (lt_of_not_ge hn)
      exact nb_no_strict_dominator (normTO η y) (3 / 5) x
        (by norm_num) (by norm_num) hr.2.1 hc
    exact ⟨hbound, hxy.trans hbound⟩
  · have hbound : y ≤ (1 - η) / (2 - η) := by
      by_contra hn
      have hc := to_strict_dominator_of_large_max hη0 hη1 hy.1 hy.2 hx.1 hx.2
        hyx ⟨hr.1.2, hr.1.1⟩ (lt_of_not_ge hn)
      exact nb_no_strict_dominator (normTO η x) (3 / 5) y
        (by norm_num) (by norm_num) hr.2.2 hc
    exact ⟨hyx.trans hbound, hbound⟩

theorem nbOT_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    IsNBEqOT 1 1 0 η (3 / 5) x y ↔ x = 1 / 5 ∧ y = 1 / 5 := by
  constructor
  · intro hr
    obtain ⟨hxb, hyb⟩ := nbOT_bounds hη0 hη1 hr
    have hx0 : 0 ≤ x := hr.2.1.1.1.1
    have hy0 : 0 ≤ y := hr.2.2.1.1.1
    have hx := unitOT_shape (a := 1) (b := 1) (c := 0) (y := x)
      (by norm_num) (by norm_num) hη0 hη1 hx0 (by simpa using hxb)
    have hy := unitOT_shape (a := 1) (b := 1) (c := 0) (y := y)
      (by norm_num) (by norm_num) hη0 hη1 hy0 (by simpa using hyb)
    apply (S11KSEquilibria.ksOT_iff hη0 hη1 x y).mp
    exact ⟨hr.1, (hy.ks_iff x).mpr ((hy.nb_three_fifths_iff x).mp hr.2.1),
      (hx.ks_iff y).mpr ((hx.nb_three_fifths_iff y).mp hr.2.2)⟩
  · rintro ⟨rfl, rfl⟩
    exact (nbOT_at_point_iff hη0 hη1 (3 / 5)).mpr rfl

theorem nbTO_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    IsNBEqTO 1 1 0 η (3 / 5) x y ↔
      x = (1 - η) / (5 - η) ∧ y = (1 - η) / (5 - η) := by
  constructor
  · intro hr
    obtain ⟨hxb, hyb⟩ := nbTO_bounds hη0 hη1 hr
    have hx0 : 0 ≤ x := hr.2.1.1.1.1
    have hy0 : 0 ≤ y := hr.2.2.1.1.1
    have hcut : (1 - η) / (2 - η) ≤ 1 - η := by
      apply (div_le_iff₀ (by linarith : 0 < 2 - η)).mpr
      nlinarith [sq_nonneg (1 - η)]
    have hx := unitTO_shape (a := 1) (b := 1) (c := 0) (y := x)
      (by norm_num) (by norm_num) hη0 hη1 hx0 (by simpa using hxb.trans hcut)
    have hy := unitTO_shape (a := 1) (b := 1) (c := 0) (y := y)
      (by norm_num) (by norm_num) hη0 hη1 hy0 (by simpa using hyb.trans hcut)
    apply (S11KSEquilibria.ksTO_iff hη0 hη1 x y).mp
    exact ⟨hr.1, (hy.ks_iff x).mpr ((hy.nb_three_fifths_iff x).mp hr.2.1),
      (hx.ks_iff y).mpr ((hx.nb_three_fifths_iff y).mp hr.2.2)⟩
  · rintro ⟨rfl, rfl⟩
    exact (nbTO_at_point_iff hη0 hη1 (3 / 5)).mpr rfl

end S11NBEquilibria
end



set_option autoImplicit false
noncomputable section
open CompetingKS
open scoped Pointwise

namespace S11Scaling

/-- A change of contract coordinates with a common positive profit scale. -/
structure Scaling (U V : BargainingUnit) (e : ℝ ≃ ℝ) (k : ℝ) : Prop where
  scale_pos : 0 < k
  contract : ∀ x, e x ∈ U.W ↔ x ∈ V.W
  seller : ∀ x, U.S (e x) = k * V.S x
  buyer : ∀ x, U.B (e x) = k * V.B x
  disagree_seller : U.D = k * V.D
  disagree_buyer : U.d = k * V.d

variable {U V : BargainingUnit} {e : ℝ ≃ ℝ} {k : ℝ} (h : Scaling U V e k)

include h

theorem Scaling.seller_surplus (x : ℝ) :
    U.S (e x) - U.D = k * (V.S x - V.D) := by
  rw [h.seller, h.disagree_seller]
  ring

theorem Scaling.buyer_surplus (x : ℝ) :
    U.B (e x) - U.d = k * (V.B x - V.d) := by
  rw [h.buyer, h.disagree_buyer]
  ring

theorem Scaling.ir_iff (x : ℝ) : U.IsIR (e x) ↔ V.IsIR x := by
  simp only [BargainingUnit.IsIR, h.contract, h.seller, h.buyer,
    h.disagree_seller, h.disagree_buyer, mul_le_mul_iff_right₀ h.scale_pos]

theorem Scaling.dominated_iff (x : ℝ) : U.IsDominated (e x) ↔ V.IsDominated x := by
  constructor
  · rintro ⟨w, hw, hS, hB, hs⟩
    obtain ⟨y, rfl⟩ := e.surjective w
    refine ⟨y, (h.contract y).mp hw, ?_, ?_, ?_⟩
    · simpa only [h.seller, mul_le_mul_iff_right₀ h.scale_pos] using hS
    · simpa only [h.buyer, mul_le_mul_iff_right₀ h.scale_pos] using hB
    · simpa only [h.seller, h.buyer, mul_lt_mul_iff_right₀ h.scale_pos] using hs
  · rintro ⟨y, hy, hS, hB, hs⟩
    refine ⟨e y, (h.contract y).mpr hy, ?_, ?_, ?_⟩
    · simpa only [h.seller, mul_le_mul_iff_right₀ h.scale_pos] using hS
    · simpa only [h.buyer, mul_le_mul_iff_right₀ h.scale_pos] using hB
    · simpa only [h.seller, h.buyer, mul_lt_mul_iff_right₀ h.scale_pos] using hs

theorem Scaling.pareto_iff (x : ℝ) : U.IsPareto (e x) ↔ V.IsPareto x := by
  simp only [BargainingUnit.IsPareto, h.contract, h.dominated_iff]

theorem Scaling.seller_set :
    U.S '' {w ∈ U.W | U.d ≤ U.B w} = k • (V.S '' {x ∈ V.W | V.d ≤ V.B x}) := by
  ext z
  constructor
  · rintro ⟨w, hw, hz⟩
    obtain ⟨x, rfl⟩ := e.surjective w
    rw [Set.mem_smul_set]
    refine ⟨V.S x, ⟨x, ⟨(h.contract x).mp hw.1, ?_⟩, rfl⟩, ?_⟩
    · simpa only [h.buyer, h.disagree_buyer, mul_le_mul_iff_right₀ h.scale_pos] using hw.2
    · change k * V.S x = z
      exact (h.seller x).symm.trans hz
  · rw [Set.mem_smul_set]
    rintro ⟨v, ⟨x, hx, rfl⟩, hz⟩
    refine ⟨e x, ⟨(h.contract x).mpr hx.1, ?_⟩, ?_⟩
    · simpa only [h.buyer, h.disagree_buyer, mul_le_mul_iff_right₀ h.scale_pos] using hx.2
    · exact (h.seller x).trans hz

theorem Scaling.buyer_set :
    U.B '' {w ∈ U.W | U.D ≤ U.S w} = k • (V.B '' {x ∈ V.W | V.D ≤ V.S x}) := by
  ext z
  constructor
  · rintro ⟨w, hw, hz⟩
    obtain ⟨x, rfl⟩ := e.surjective w
    rw [Set.mem_smul_set]
    refine ⟨V.B x, ⟨x, ⟨(h.contract x).mp hw.1, ?_⟩, rfl⟩, ?_⟩
    · simpa only [h.seller, h.disagree_seller, mul_le_mul_iff_right₀ h.scale_pos] using hw.2
    · change k * V.B x = z
      exact (h.buyer x).symm.trans hz
  · rw [Set.mem_smul_set]
    rintro ⟨v, ⟨x, hx, rfl⟩, hz⟩
    refine ⟨e x, ⟨(h.contract x).mpr hx.1, ?_⟩, ?_⟩
    · simpa only [h.seller, h.disagree_seller, mul_le_mul_iff_right₀ h.scale_pos] using hx.2
    · exact (h.buyer x).trans hz

theorem Scaling.sbar : U.Sbar = k * V.Sbar := by
  unfold BargainingUnit.Sbar
  rw [h.seller_set]
  exact Real.sSup_smul_of_nonneg h.scale_pos.le _

theorem Scaling.bbar : U.Bbar = k * V.Bbar := by
  unfold BargainingUnit.Bbar
  rw [h.buyer_set]
  exact Real.sSup_smul_of_nonneg h.scale_pos.le _

theorem Scaling.ks_iff (x : ℝ) : U.IsKSResponse (e x) ↔ V.IsKSResponse x := by
  unfold BargainingUnit.IsKSResponse
  rw [h.ir_iff, h.pareto_iff, h.buyer_surplus, h.seller_surplus,
    h.sbar, h.bbar, h.disagree_seller, h.disagree_buyer]
  have hk : k * k ≠ 0 := mul_ne_zero (ne_of_gt h.scale_pos) (ne_of_gt h.scale_pos)
  constructor
  · rintro ⟨hir, hp, he⟩
    refine ⟨hir, hp, ?_⟩
    apply mul_left_cancel₀ hk
    calc
      (k * k) * ((V.B x - V.d) * (V.Sbar - V.D)) =
        k * (V.B x - V.d) * (k * V.Sbar - k * V.D) := by ring
      _ = k * (V.S x - V.D) * (k * V.Bbar - k * V.d) := he
      _ = (k * k) * ((V.S x - V.D) * (V.Bbar - V.d)) := by ring
  · rintro ⟨hir, hp, he⟩
    refine ⟨hir, hp, ?_⟩
    calc
      k * (V.B x - V.d) * (k * V.Sbar - k * V.D) =
        (k * k) * ((V.B x - V.d) * (V.Sbar - V.D)) := by ring
      _ = (k * k) * ((V.S x - V.D) * (V.Bbar - V.d)) := by rw [he]
      _ = k * (V.S x - V.D) * (k * V.Bbar - k * V.d) := by ring

theorem Scaling.nash_product (θ x : ℝ) (hx : V.IsIR x) :
    U.nashProduct θ (e x) = k * V.nashProduct θ x := by
  unfold BargainingUnit.nashProduct
  rw [h.buyer_surplus, h.seller_surplus,
    Real.mul_rpow h.scale_pos.le (sub_nonneg.mpr hx.2.2),
    Real.mul_rpow h.scale_pos.le (sub_nonneg.mpr hx.2.1)]
  calc
    k ^ θ * (V.B x - V.d) ^ θ * (k ^ (1 - θ) * (V.S x - V.D) ^ (1 - θ)) =
      (k ^ θ * k ^ (1 - θ)) * ((V.B x - V.d) ^ θ * (V.S x - V.D) ^ (1 - θ)) := by ring
    _ = _ := by rw [← Real.rpow_add h.scale_pos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]

theorem Scaling.nb_iff (θ x : ℝ) : U.IsNBResponse θ (e x) ↔ V.IsNBResponse θ x := by
  constructor
  · rintro ⟨hir, hm⟩
    have hx := (h.ir_iff x).mp hir
    refine ⟨hx, ?_⟩
    intro y hy
    have hm' := hm (e y) ((h.ir_iff y).mpr hy)
    rw [h.nash_product θ y hy, h.nash_product θ x hx] at hm'
    exact (mul_le_mul_iff_right₀ h.scale_pos).mp hm'
  · rintro ⟨hir, hm⟩
    refine ⟨(h.ir_iff x).mpr hir, ?_⟩
    intro w hw
    obtain ⟨y, rfl⟩ := e.surjective w
    have hy := (h.ir_iff y).mp hw
    rw [h.nash_product θ y hy, h.nash_product θ x hir]
    exact mul_le_mul_of_nonneg_left (hm y hy) h.scale_pos.le

end S11Scaling
end


set_option autoImplicit false
noncomputable section
namespace S11Normalize
open CompetingKS

def priceMap (a c x : ℝ) : ℝ := c + (a - c) * x

theorem gap_priceMap (a c x : ℝ) : a - priceMap a c x = (a - c) * (1 - x) := by
  unfold priceMap
  ring

theorem priceMap_mem {a c x : ℝ} (hac : c < a) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    priceMap a c x ∈ Set.Icc c a := by
  unfold priceMap
  have hd : 0 < a - c := sub_pos.mpr hac
  constructor <;> nlinarith [mul_nonneg hd.le hx.1, mul_nonneg hd.le (sub_nonneg.mpr hx.2)]

theorem inCHat_priceMap {a c η x y : ℝ} (hac : c < a) :
    InCHat a η (priceMap a c x) (priceMap a c y) ↔ InCHat 1 η x y := by
  have hd : 0 < a - c := sub_pos.mpr hac
  unfold InCHat
  rw [gap_priceMap, gap_priceMap]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h1]
    · apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h2]
  · rintro ⟨h1,h2⟩
    constructor
    · have hp := (mul_le_mul_iff_right₀ hd).2 h1
      nlinarith only [hp]
    · have hp := (mul_le_mul_iff_right₀ hd).2 h2
      nlinarith only [hp]

theorem inCCheck_priceMap {a c η x y : ℝ} (hac : c < a) :
    InCCheck a η (priceMap a c x) (priceMap a c y) ↔ InCCheck 1 η x y := by
  have hd : 0 < a - c := sub_pos.mpr hac
  unfold InCCheck
  rw [gap_priceMap, gap_priceMap]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h1]
    · apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h2]
  · rintro ⟨h1,h2⟩
    constructor
    · have hp := (mul_le_mul_iff_right₀ hd).2 h1
      nlinarith only [hp]
    · have hp := (mul_le_mul_iff_right₀ hd).2 h2
      nlinarith only [hp]

theorem qOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    qOT a b η (priceMap a c x) (priceMap a c y) =
      ((a - c) / b) * qOT 1 1 η x y := by
  have hd : 0 < a - c := sub_pos.mpr hac
  have hb' := ne_of_gt hb
  have hn : 4 - η ^ 2 ≠ 0 := by nlinarith
  have h1 : 2 * ((a - c) * (1 - x)) ≤ η * ((a - c) * (1 - y)) ↔
      2 * (1 - x) ≤ η * (1 - y) := by
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h]
    · intro h
      have hp := (mul_le_mul_iff_right₀ hd).2 h
      nlinarith only [hp]
  have h2 : 2 * ((a - c) * (1 - y)) ≤ η * ((a - c) * (1 - x)) ↔
      2 * (1 - y) ≤ η * (1 - x) := by
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h]
    · intro h
      have hp := (mul_le_mul_iff_right₀ hd).2 h
      nlinarith only [hp]
  unfold qOT
  rw [gap_priceMap, gap_priceMap]
  simp only [h1, h2]
  split_ifs <;> field_simp
  all_goals ring

theorem qTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    qTO a b η (priceMap a c x) (priceMap a c y) =
      ((a - c) / b) * qTO 1 1 η x y := by
  have hd : 0 < a - c := sub_pos.mpr hac
  have hb' := ne_of_gt hb
  have hn : 1 - η ^ 2 ≠ 0 := by nlinarith
  have h1 : ((a - c) * (1 - x)) ≤ η * ((a - c) * (1 - y)) ↔
      1 - x ≤ η * (1 - y) := by
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h]
    · intro h
      have hp := (mul_le_mul_iff_right₀ hd).2 h
      nlinarith only [hp]
  have h2 : ((a - c) * (1 - y)) ≤ η * ((a - c) * (1 - x)) ↔
      1 - y ≤ η * (1 - x) := by
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ hd).1
      nlinarith only [h]
    · intro h
      have hp := (mul_le_mul_iff_right₀ hd).2 h
      nlinarith only [hp]
  unfold qTO
  rw [gap_priceMap, gap_priceMap]
  simp only [h1, h2]
  split_ifs <;> field_simp
  all_goals ring

theorem priceMap_inverse {a c : ℝ} (hac : c < a) (w : ℝ) :
    priceMap a c ((w - c) / (a - c)) = w := by
  have hd : a - c ≠ 0 := ne_of_gt (sub_pos.mpr hac)
  unfold priceMap
  field_simp
  ring

theorem inverse_priceMap {a c : ℝ} (hac : c < a) (x : ℝ) :
    (priceMap a c x - c) / (a - c) = x := by
  have hd : a - c ≠ 0 := ne_of_gt (sub_pos.mpr hac)
  unfold priceMap
  field_simp
  ring

def priceEquiv {a c : ℝ} (hac : c < a) : ℝ ≃ ℝ where
  toFun := priceMap a c
  invFun := fun w => (w - c) / (a - c)
  left_inv := inverse_priceMap hac
  right_inv := priceMap_inverse hac

theorem priceMap_mem_iff {a c x : ℝ} (hac : c < a) :
    priceMap a c x ∈ Set.Icc c a ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : 0 < a - c := sub_pos.mpr hac
  constructor
  · intro h
    constructor
    · apply (mul_le_mul_iff_right₀ hd).1
      dsimp [priceMap] at h
      nlinarith only [h.1]
    · apply (mul_le_mul_iff_right₀ hd).1
      dsimp [priceMap] at h
      nlinarith only [h.2]
  · exact priceMap_mem hac

def profitScale (a b c : ℝ) : ℝ := (a - c) ^ 2 / b

theorem profitScale_pos {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    0 < profitScale a b c := by
  unfold profitScale
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hac)) hb

theorem price_scaled {a b c η : ℝ} (hb : 0 < b) (x y : ℝ) :
    price a b η (((a - c) / b) * x) (((a - c) / b) * y) =
      priceMap a c (price 1 1 η x y) := by
  have hb' : b ≠ 0 := ne_of_gt hb
  unfold price priceMap
  field_simp
  ring

theorem priceOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    priceOT a b η (priceMap a c x) (priceMap a c y) =
      priceMap a c (priceOT 1 1 η x y) := by
  unfold priceOT
  rw [qOT_priceMap hac hb hη0 hη1, qOT_priceMap hac hb hη0 hη1]
  exact price_scaled hb _ _

theorem priceTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    priceTO a b η (priceMap a c x) (priceMap a c y) =
      priceMap a c (priceTO 1 1 η x y) := by
  unfold priceTO
  rw [qTO_priceMap hac hb hη0 hη1, qTO_priceMap hac hb hη0 hη1]
  exact price_scaled hb _ _

theorem ROT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    ROT a b c η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * ROT 1 1 0 η x y := by
  unfold ROT
  rw [qOT_priceMap hac hb hη0 hη1]
  unfold priceMap profitScale
  ring

theorem RTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    RTO a b c η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * RTO 1 1 0 η x y := by
  unfold RTO
  rw [qTO_priceMap hac hb hη0 hη1]
  unfold priceMap profitScale
  ring

theorem rOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    rOT a b η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * rOT 1 1 η x y := by
  unfold rOT
  rw [qOT_priceMap hac hb hη0 hη1, priceOT_priceMap hac hb hη0 hη1]
  unfold priceMap profitScale
  ring

theorem rTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    rTO a b η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * rTO 1 1 η x y := by
  unfold rTO
  rw [qTO_priceMap hac hb hη0 hη1, priceTO_priceMap hac hb hη0 hη1]
  unfold priceMap profitScale
  ring

theorem supplierOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    supplierOT a b c η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * supplierOT 1 1 0 η x y := by
  unfold supplierOT
  rw [ROT_priceMap hac hb hη0 hη1, ROT_priceMap hac hb hη0 hη1]
  ring

theorem retailerOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    retailerOT a b η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * retailerOT 1 1 η x y :=
  rOT_priceMap hac hb hη0 hη1 x y

theorem supplierTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    supplierTO a b c η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * supplierTO 1 1 0 η x y :=
  RTO_priceMap hac hb hη0 hη1 x y

theorem retailerTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    retailerTO a b η (priceMap a c x) (priceMap a c y) =
      profitScale a b c * retailerTO 1 1 η x y := by
  unfold retailerTO
  rw [rTO_priceMap hac hb hη0 hη1, rTO_priceMap hac hb hη0 hη1]
  ring

theorem disagreeOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (y : ℝ) :
    disagreeOT a b c η (priceMap a c y) =
      profitScale a b c * disagreeOT 1 1 0 η y := by
  have hm : a - η * (a - priceMap a c y) / 2 =
      priceMap a c (1 - η * (1 - y) / 2) := by
    unfold priceMap
    ring
  unfold disagreeOT
  rw [hm]
  exact ROT_priceMap hac hb hη0 hη1 _ _

theorem disagreeTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (y : ℝ) :
    disagreeTO a b η (priceMap a c y) =
      profitScale a b c * disagreeTO 1 1 η y := by
  have hm : a - η * (a - priceMap a c y) =
      priceMap a c (1 - η * (1 - y)) := by
    unfold priceMap
    ring
  unfold disagreeTO
  rw [hm]
  exact rTO_priceMap hac hb hη0 hη1 _ _

theorem scalingOT {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (y : ℝ) :
    S11Scaling.Scaling (unitOT a b c η (priceMap a c y)) (normOT η y)
      (priceEquiv hac) (profitScale a b c) where
  scale_pos := profitScale_pos hac hb
  contract := fun _ => priceMap_mem_iff hac
  seller := fun x => supplierOT_priceMap hac hb hη0 hη1 x y
  buyer := fun x => retailerOT_priceMap hac hb hη0 hη1 x y
  disagree_seller := disagreeOT_priceMap hac hb hη0 hη1 y
  disagree_buyer := by simp [unitOT]

theorem scalingTO {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (y : ℝ) :
    S11Scaling.Scaling (unitTO a b c η (priceMap a c y)) (normTO η y)
      (priceEquiv hac) (profitScale a b c) where
  scale_pos := profitScale_pos hac hb
  contract := fun _ => priceMap_mem_iff hac
  seller := fun x => supplierTO_priceMap hac hb hη0 hη1 x y
  buyer := fun x => retailerTO_priceMap hac hb hη0 hη1 x y
  disagree_seller := by simp [unitTO]
  disagree_buyer := disagreeTO_priceMap hac hb hη0 hη1 y

theorem ksOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (x y : ℝ) :
    IsKSEqOT a b c η (priceMap a c x) (priceMap a c y) ↔ IsKSEqOT 1 1 0 η x y := by
  unfold IsKSEqOT
  exact and_congr (inCHat_priceMap hac)
    (and_congr ((scalingOT hac hb hη0 hη1 y).ks_iff x)
      ((scalingOT hac hb hη0 hη1 x).ks_iff y))

theorem nbOT_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (θ x y : ℝ) :
    IsNBEqOT a b c η θ (priceMap a c x) (priceMap a c y) ↔
      IsNBEqOT 1 1 0 η θ x y := by
  unfold IsNBEqOT
  exact and_congr (inCHat_priceMap hac)
    (and_congr ((scalingOT hac hb hη0 hη1 y).nb_iff θ x)
      ((scalingOT hac hb hη0 hη1 x).nb_iff θ y))

theorem ksTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (x y : ℝ) :
    IsKSEqTO a b c η (priceMap a c x) (priceMap a c y) ↔ IsKSEqTO 1 1 0 η x y := by
  unfold IsKSEqTO
  exact and_congr (inCCheck_priceMap hac)
    (and_congr ((scalingTO hac hb hη0 hη1 y).ks_iff x)
      ((scalingTO hac hb hη0 hη1 x).ks_iff y))

theorem nbTO_priceMap {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (θ x y : ℝ) :
    IsNBEqTO a b c η θ (priceMap a c x) (priceMap a c y) ↔
      IsNBEqTO 1 1 0 η θ x y := by
  unfold IsNBEqTO
  exact and_congr (inCCheck_priceMap hac)
    (and_congr ((scalingTO hac hb hη0 hη1 y).nb_iff θ x)
      ((scalingTO hac hb hη0 hη1 x).nb_iff θ y))

theorem ksOT_normalize {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (w₁ w₂ : ℝ) :
    IsKSEqOT a b c η w₁ w₂ ↔
      IsKSEqOT 1 1 0 η ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c)) := by
  simpa only [priceMap_inverse hac] using
    ksOT_priceMap hac hb hη0 hη1 ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c))

theorem nbOT_normalize {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (θ w₁ w₂ : ℝ) :
    IsNBEqOT a b c η θ w₁ w₂ ↔
      IsNBEqOT 1 1 0 η θ ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c)) := by
  simpa only [priceMap_inverse hac] using
    nbOT_priceMap hac hb hη0 hη1 θ ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c))

theorem ksTO_normalize {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (w₁ w₂ : ℝ) :
    IsKSEqTO a b c η w₁ w₂ ↔
      IsKSEqTO 1 1 0 η ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c)) := by
  simpa only [priceMap_inverse hac] using
    ksTO_priceMap hac hb hη0 hη1 ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c))

theorem nbTO_normalize {a b c η : ℝ} (hac : c < a) (hb : 0 < b)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (θ w₁ w₂ : ℝ) :
    IsNBEqTO a b c η θ w₁ w₂ ↔
      IsNBEqTO 1 1 0 η θ ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c)) := by
  simpa only [priceMap_inverse hac] using
    nbTO_priceMap hac hb hη0 hη1 θ ((w₁ - c) / (a - c)) ((w₂ - c) / (a - c))

theorem normalize_eq_iff {a c : ℝ} (hac : c < a) (w t : ℝ) :
    (w - c) / (a - c) = t ↔ w = priceMap a c t := by
  constructor
  · intro h
    rw [← h]
    exact (priceMap_inverse hac w).symm
  · rintro rfl
    exact inverse_priceMap hac t

end S11Normalize
end


open CompetingKS

/-- Proposition 2 (Simultaneous Bargaining without Contingency), Feng, Li, Shanthikumar,
*Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution*, accepted
manuscript (Management Science, July 3, 2021), SSRN 3447674, pp.19–20.

For every `a > c`, `b > 0`. In the one-to-two channel, for every `η ∈ [0, 1]`, with
`ŵ = c + (a - c)/5`: the simultaneous KS equilibrium exists, is unique and equals `(ŵ, ŵ)`; `(ŵ, ŵ)`
is a simultaneous NB equilibrium with retailer power `θ ∈ [0, 1]` exactly when `θ = 3/5`; and the NB
equilibrium at `θ = 3/5` exists, is unique and equals `(ŵ, ŵ)`. In the two-to-one channel, for every
`η ∈ [0, 1)`, with `w̌ = c + (1 - η)(a - c)/(5 - η)`: the same three statements.

**Formalization Note** The two-to-one channel excludes `η = 1`, where the claimed `w̌ = c` lies on
the diagonal on which Lemma 1(ii) does not define `q*`. Equilibria are `IsKSEqOT`, `IsNBEqOT`,
`IsKSEqTO`, `IsNBEqTO`; the KS solution is `IsKSResponse`, individual rationality, Pareto optimality
and equation (2). -/
theorem solution {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      (∀ w₁ w₂ : ℝ, IsKSEqOT a b c η w₁ w₂ ↔ w₁ = c + (a - c) / 5 ∧ w₂ = c + (a - c) / 5) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (IsNBEqOT a b c η θ (c + (a - c) / 5) (c + (a - c) / 5) ↔ θ = 3 / 5)) ∧
      (∀ w₁ w₂ : ℝ, IsNBEqOT a b c η (3 / 5) w₁ w₂ ↔
        w₁ = c + (a - c) / 5 ∧ w₂ = c + (a - c) / 5)) ∧
    (∀ η : ℝ, 0 ≤ η → η < 1 →
      (∀ w₁ w₂ : ℝ, IsKSEqTO a b c η w₁ w₂ ↔
        w₁ = c + (1 - η) * (a - c) / (5 - η) ∧ w₂ = c + (1 - η) * (a - c) / (5 - η)) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (IsNBEqTO a b c η θ (c + (1 - η) * (a - c) / (5 - η))
          (c + (1 - η) * (a - c) / (5 - η)) ↔ θ = 3 / 5)) ∧
      (∀ w₁ w₂ : ℝ, IsNBEqTO a b c η (3 / 5) w₁ w₂ ↔
        w₁ = c + (1 - η) * (a - c) / (5 - η) ∧ w₂ = c + (1 - η) * (a - c) / (5 - η))) := by
  have hK : 0 < a - c := sub_pos.mpr hac
  have hnorm (w z : ℝ) : (w - c) / (a - c) = z ↔ w = c + (a - c) * z := by
    rw [div_eq_iff hK.ne']
    constructor <;> intro he <;> nlinarith only [he]
  have hot (w : ℝ) : (w - c) / (a - c) = 1 / 5 ↔ w = c + (a - c) / 5 := by
    have he : c + (a - c) * (1 / 5 : ℝ) = c + (a - c) / 5 := by ring
    rw [hnorm, he]
  have hto (w η : ℝ) : (w - c) / (a - c) = (1 - η) / (5 - η) ↔
      w = c + (1 - η) * (a - c) / (5 - η) := by
    have he : c + (a - c) * ((1 - η) / (5 - η)) =
        c + (1 - η) * (a - c) / (5 - η) := by ring
    rw [hnorm, he]
  constructor
  · intro η hη0 hη1
    refine ⟨?_, ?_, ?_⟩
    · intro w₁ w₂
      rw [S11Normalize.ksOT_normalize hac hb hη0 hη1 w₁ w₂,
        S11KSEquilibria.ksOT_iff hη0 hη1, hot, hot]
    · intro θ hθ0 hθ1
      rw [S11Normalize.nbOT_normalize hac hb hη0 hη1 θ]
      have he : (c + (a - c) / 5 - c) / (a - c) = 1 / 5 := (hot _).mpr rfl
      simpa only [he] using S11NBEquilibria.nbOT_at_point_iff hη0 hη1 θ
    · intro w₁ w₂
      rw [S11Normalize.nbOT_normalize hac hb hη0 hη1 (3 / 5) w₁ w₂,
        S11NBEquilibria.nbOT_iff hη0 hη1, hot, hot]
  · intro η hη0 hη1
    refine ⟨?_, ?_, ?_⟩
    · intro w₁ w₂
      rw [S11Normalize.ksTO_normalize hac hb hη0 hη1 w₁ w₂,
        S11KSEquilibria.ksTO_iff hη0 hη1, hto, hto]
    · intro θ hθ0 hθ1
      rw [S11Normalize.nbTO_normalize hac hb hη0 hη1 θ]
      have he : (c + (1 - η) * (a - c) / (5 - η) - c) / (a - c) =
          (1 - η) / (5 - η) := (hto _ η).mpr rfl
      simpa only [he] using S11NBEquilibria.nbTO_at_point_iff hη0 hη1 θ
    · intro w₁ w₂
      rw [S11Normalize.nbTO_normalize hac hb hη0 hη1 (3 / 5) w₁ w₂,
        S11NBEquilibria.nbTO_iff hη0 hη1, hto, hto]




#print axioms solution
