-- Prove2me | solution 1 for BirkhoffGlobalSection.position_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T20:00:47.027606+00:00
-- url     : https://prove2.me/submissions/ea8a5189-d215-48ac-b9a6-3fbebfc338a4

import Definitions.Def_BirkhoffGlobalSection

noncomputable section

namespace BirkhoffGlobalSection

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

end BirkhoffGlobalSection

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : BirkhoffGlobalSection.Phase)
    (hs : s ∈ BirkhoffGlobalSection.leftEnergyComponent μ c) :
    2 * BirkhoffGlobalSection.zNormSq s ≤ 3 / 5 :=
  BirkhoffGlobalSection.position_bound_proof μ c hμ0 hμhalf hc s hs
