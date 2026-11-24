-- Prove2me | solution 1 for BirkhoffRestrictedThreeBody.momentum_bound
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T06:23:59.275371+00:00
-- url     : https://prove2.me/submissions/92a687b6-6a7e-417e-b7dc-f31cb4590d45

import Definitions.Def_BirkhoffRestrictedThreeBody


noncomputable section

namespace BirkhoffRestrictedThreeBody

private lemma leftCollisionPoint_mem_regularEnergyLocus
    (μ c : ℝ) (hμhalf : μ ≤ 1 / 2) :
    leftCollisionPoint μ ∈ regularEnergyLocus μ c := by
  constructor
  · unfold leviCivitaHamiltonian wNormSq zNormSq leftCollisionPoint
    simp
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - μ)]
    ring
  · unfold secondCollisionDistanceSq leftCollisionPoint
    norm_num

private lemma boundary_energy_positive (μ c : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc : 21 / 10 ≤ c)
    (s : Phase) (hz : zNormSq s = 3 / 10)
    (hD : 0 < secondCollisionDistanceSq s) :
    0 < leviCivitaHamiltonian μ c s := by
  have ha0 : 0 ≤ (s 0) ^ 2 := sq_nonneg _
  have hb0 : 0 ≤ (s 1) ^ 2 := sq_nonneg _
  have hab : (s 0) ^ 2 + (s 1) ^ 2 = 3 / 10 := by
    simpa [zNormSq] using hz
  have ha_le : (s 0) ^ 2 ≤ 3 / 10 := by linarith
  have hDformula : secondCollisionDistanceSq s = 64 / 25 - 8 * (s 0) ^ 2 := by
    unfold secondCollisionDistanceSq
    nlinarith [sq_nonneg (2 * ((s 0) ^ 2 - (s 1) ^ 2) - 1),
      sq_nonneg (4 * s 0 * s 1)]
  let T : ℝ := Real.sqrt (secondCollisionDistanceSq s)
  have hTpos : 0 < T := by
    exact Real.sqrt_pos.2 hD
  have hTsq : T ^ 2 = secondCollisionDistanceSq s := by
    exact Real.sq_sqrt hD.le
  let L : ℝ := 397 / 2000 + 3 / 5 * (s 0) ^ 2
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  have hquadpos :
      0 < 1440000 * ((s 0) ^ 2) ^ 2 + 924000 * (s 0) ^ 2 + 129913 := by
    positivity
  have hfactor : 0 ≤
      (3 - 10 * (s 0) ^ 2) *
        (1440000 * ((s 0) ^ 2) ^ 2 + 924000 * (s 0) ^ 2 + 129913) :=
    mul_nonneg (by linarith) hquadpos.le
  have hpoly : (3 / 20 : ℝ) ^ 2 < L ^ 2 * secondCollisionDistanceSq s := by
    rw [hDformula]
    dsimp [L]
    ring_nf at hfactor ⊢
    linarith
  have hprod_sq : (3 / 20 : ℝ) ^ 2 < (L * T) ^ 2 := by
    rw [mul_pow, hTsq]
    exact hpoly
  have hprod : (3 / 20 : ℝ) < L * T := by
    nlinarith [mul_pos hLpos hTpos]
  have hhalf : 0 < L - 3 / (20 * T) := by
    have hfrac : (3 / 20 : ℝ) / T < L := by
      apply (div_lt_iff₀ hTpos).2
      nlinarith
    have heq : (3 / 20 : ℝ) / T = 3 / (20 * T) := by
      field_simp [ne_of_gt hTpos]
    linarith
  let C : ℝ :=
    (3 / 5 + μ) ^ 2 * (s 1) ^ 2 + (3 / 5 - μ) ^ 2 * (s 0) ^ 2
  let R : ℝ :=
    wNormSq s / 2 + 2 * zNormSq s * (s 0 * s 3 - s 1 * s 2) -
      μ * (s 0 * s 3 + s 1 * s 2)
  let Q : ℝ :=
    63 / 100 - (1 - μ) / 2 -
      1 / 2 * C -
      (3 * μ / 10) / T
  have hQdecomp :
      Q = (1 - 2 * μ) * (19 / 250) + 2 * μ * (L - 3 / (20 * T)) +
        3 / 20 * μ * (1 / 2 - μ) := by
    dsimp [Q, C, L]
    rw [show (s 1) ^ 2 = 3 / 10 - (s 0) ^ 2 by linarith]
    field_simp [ne_of_gt hTpos]
    ring
  have hfirst : 0 ≤ (1 - 2 * μ) * (19 / 250 : ℝ) :=
    mul_nonneg (by linarith) (by norm_num)
  have hsecond : 0 ≤ 2 * μ * (L - 3 / (20 * T)) :=
    mul_nonneg (mul_nonneg (by norm_num) hμ0) hhalf.le
  have hconvex : 0 <
      (1 - 2 * μ) * (19 / 250 : ℝ) + 2 * μ * (L - 3 / (20 * T)) := by
    by_cases hμ : μ = 0
    · subst μ
      norm_num
    · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
      have hspos : 0 < 2 * μ * (L - 3 / (20 * T)) :=
        mul_pos (mul_pos (by norm_num) hμpos) hhalf
      linarith only [hfirst, hspos]
  have hlast : 0 ≤ 3 / 20 * μ * (1 / 2 - μ) := by positivity
  have hQpos : 0 < Q := by rw [hQdecomp]; linarith only [hconvex, hlast]
  have hwlower : -(1 / 2) * C ≤ R := by
    dsimp [C, R]
    unfold wNormSq
    rw [hz]
    nlinarith [sq_nonneg (s 2 - (3 / 5 + μ) * s 1),
      sq_nonneg (s 3 + (3 / 5 - μ) * s 0)]
  have hcpart : (63 / 100 : ℝ) ≤ c * (3 / 10) := by
    nlinarith only [hc]
  have hbasele :
      63 / 100 - (1 - μ) / 2 - 1 / 2 * C - (3 * μ / 10) / T ≤
        R + c * (3 / 10) - (1 - μ) / 2 - (3 * μ / 10) / T := by
    linarith only [hwlower, hcpart]
  have hQle : Q ≤ leviCivitaHamiltonian μ c s := by
    calc
      Q = 63 / 100 - (1 - μ) / 2 - 1 / 2 * C - (3 * μ / 10) / T := rfl
      _ ≤ R + c * (3 / 10) - (1 - μ) / 2 - (3 * μ / 10) / T := hbasele
      _ = leviCivitaHamiltonian μ c s := by
        dsimp [R]
        unfold leviCivitaHamiltonian
        rw [hz]
        ring
  exact lt_of_lt_of_le hQpos hQle

theorem position_bound_proof (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    2 * zNormSq s ≤ 3 / 5 := by
  by_contra hbound
  have hzlarge : 3 / 10 < zNormSq s := by linarith
  have hbase_locus := leftCollisionPoint_mem_regularEnergyLocus μ c hμhalf
  have hbase : leftCollisionPoint μ ∈ leftEnergyComponent μ c :=
    mem_connectedComponentIn hbase_locus
  have hzcont : Continuous zNormSq := by
    unfold zNormSq
    fun_prop
  have hmid : (3 / 10 : ℝ) ∈ zNormSq '' leftEnergyComponent μ c :=
    isPreconnected_connectedComponentIn.intermediate_value hbase hs hzcont.continuousOn
      (by
        constructor
        · norm_num [zNormSq, leftCollisionPoint]
        · exact hzlarge.le)
  obtain ⟨t, ht, hzt⟩ := hmid
  have ht_locus : t ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset _ _ ht
  have hpositive := boundary_energy_positive μ c hμ0 hμhalf hc t hzt ht_locus.2
  exact (ne_of_gt hpositive) ht_locus.1


private lemma leftCollisionPoint_mem_regularEnergyLocus'
    (μ c : ℝ) (hμhalf : μ ≤ 1 / 2) :
    leftCollisionPoint μ ∈ regularEnergyLocus μ c := by
  constructor
  · unfold leviCivitaHamiltonian wNormSq zNormSq leftCollisionPoint
    simp
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - μ)]
    ring
  · unfold secondCollisionDistanceSq leftCollisionPoint
    norm_num

private lemma momentum_boundary_energy_positive (μ c : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc : 21 / 10 ≤ c)
    (s : Phase) (hr : zNormSq s ≤ 3 / 10) (hw : wNormSq s = 4)
    (hD : 0 < secondCollisionDistanceSq s) :
    0 < leviCivitaHamiltonian μ c s := by
  let r : ℝ := zNormSq s
  let u : ℝ := s 0 * s 3 - s 1 * s 2
  let v : ℝ := s 0 * s 3 + s 1 * s 2
  let T : ℝ := Real.sqrt (secondCollisionDistanceSq s)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    unfold zNormSq
    positivity
  have huident : u ^ 2 + (s 0 * s 2 + s 1 * s 3) ^ 2 = r * wNormSq s := by
    dsimp [u, r]
    unfold zNormSq wNormSq
    ring
  have hvident : v ^ 2 + (s 0 * s 2 - s 1 * s 3) ^ 2 = r * wNormSq s := by
    dsimp [v, r]
    unfold zNormSq wNormSq
    ring
  have husq : u ^ 2 ≤ 6 / 5 := by
    rw [hw] at huident
    nlinarith only [huident, hr, sq_nonneg (s 0 * s 2 + s 1 * s 3)]
  have hvsq : v ^ 2 ≤ 6 / 5 := by
    rw [hw] at hvident
    nlinarith only [hvident, hr, sq_nonneg (s 0 * s 2 - s 1 * s 3)]
  have hulower : -(6 / 5 : ℝ) ≤ u := by
    nlinarith only [husq, sq_nonneg (u + 6 / 5)]
  have hvupper : v ≤ (6 / 5 : ℝ) := by
    nlinarith only [hvsq, sq_nonneg (v - 6 / 5)]
  have hDformula :
      secondCollisionDistanceSq s = (1 - 2 * r) ^ 2 + 8 * (s 1) ^ 2 := by
    dsimp [r]
    unfold secondCollisionDistanceSq zNormSq
    ring
  have hDlower : (1 - 2 * r) ^ 2 ≤ secondCollisionDistanceSq s := by
    rw [hDformula]
    nlinarith only [sq_nonneg (s 1)]
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = secondCollisionDistanceSq s := Real.sq_sqrt hD.le
  have hrgap : (2 / 5 : ℝ) ≤ 1 - 2 * r := by
    dsimp [r] at hr ⊢
    linarith
  have hTlower : (2 / 5 : ℝ) ≤ T := by
    nlinarith only [hDlower, hTsq, hT0, hrgap]
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTlower
  have hmur : μ * r ≤ 3 / 20 := by
    calc
      μ * r ≤ (1 / 2) * r := mul_le_mul_of_nonneg_right hμhalf hr0
      _ ≤ (1 / 2) * (3 / 10) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 3 / 20 := by norm_num
  have hpotential : μ * r / T ≤ 3 / 8 := by
    apply (div_le_iff₀ hTpos).2
    nlinarith only [hmur, hTlower]
  have hcr : (21 / 10) * r ≤ c * r := mul_le_mul_of_nonneg_right hc hr0
  have hcross : -(12 / 5) * r ≤ 2 * r * u := by
    have := mul_le_mul_of_nonneg_left hulower (show 0 ≤ 2 * r by positivity)
    nlinarith only [this]
  have hcmix : -(9 / 100 : ℝ) ≤ c * r + 2 * r * u := by
    nlinarith only [hcr, hcross, hr]
  have hmuv : μ * v ≤ 3 / 5 := by
    by_cases hv0 : 0 ≤ v
    · calc
        μ * v ≤ (1 / 2) * (6 / 5) := mul_le_mul hμhalf hvupper hv0 (by norm_num)
        _ = 3 / 5 := by norm_num
    · have : μ * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hμ0 (le_of_not_ge hv0)
      linarith
  have hconst : -(1 - μ) / 2 ≥ -(1 / 2 : ℝ) := by linarith
  unfold leviCivitaHamiltonian
  change 0 < wNormSq s / 2 + c * r - (1 - μ) / 2 + 2 * r * u - μ * v - μ * r / T
  rw [hw]
  linarith only [hcmix, hmuv, hconst, hpotential]

theorem momentum_bound_proof (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : Phase) (hs : s ∈ leftEnergyComponent μ c) :
    Real.sqrt (wNormSq s) ≤ 2 := by
  by_contra hbound
  have hw0 : 0 ≤ wNormSq s := by
    unfold wNormSq
    positivity
  have hsqrtgt : 2 < Real.sqrt (wNormSq s) := lt_of_not_ge hbound
  have hwlarge : 4 < wNormSq s := by
    nlinarith [Real.sq_sqrt hw0]
  have hbase_locus := leftCollisionPoint_mem_regularEnergyLocus' μ c hμhalf
  have hbase : leftCollisionPoint μ ∈ leftEnergyComponent μ c :=
    mem_connectedComponentIn hbase_locus
  have hwcont : Continuous wNormSq := by
    unfold wNormSq
    fun_prop
  have hmid : (4 : ℝ) ∈ wNormSq '' leftEnergyComponent μ c :=
    isPreconnected_connectedComponentIn.intermediate_value hbase hs hwcont.continuousOn
      (by
        constructor
        · simp [wNormSq, leftCollisionPoint]
          rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - μ)]
          linarith
        · exact hwlarge.le)
  obtain ⟨t, ht, hwt⟩ := hmid
  have ht_locus : t ∈ regularEnergyLocus μ c :=
    connectedComponentIn_subset _ _ ht
  have hrt := position_bound_proof μ c hμ0 hμhalf hc t ht
  have hpositive := momentum_boundary_energy_positive μ c hμ0 hμhalf hc t
    (by linarith) hwt ht_locus.2
  exact (ne_of_gt hpositive) ht_locus.1

end BirkhoffRestrictedThreeBody

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : BirkhoffRestrictedThreeBody.Phase)
    (hs : s ∈ BirkhoffRestrictedThreeBody.leftEnergyComponent μ c) :
    Real.sqrt (BirkhoffRestrictedThreeBody.wNormSq s) ≤ 2 :=
  BirkhoffRestrictedThreeBody.momentum_bound_proof μ c hμ0 hμhalf hc s hs
