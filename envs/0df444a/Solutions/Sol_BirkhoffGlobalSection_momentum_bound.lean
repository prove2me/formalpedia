-- Prove2me | solution 1 for BirkhoffGlobalSection.momentum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T20:05:19.57299+00:00
-- url     : https://prove2.me/submissions/374b1565-5b8d-495c-bf03-9ca86c5d4492

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_position_bound

noncomputable section

namespace BirkhoffGlobalSection

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
  have hrt := position_bound μ c hμ0 hμhalf hc t ht
  have hpositive := momentum_boundary_energy_positive μ c hμ0 hμhalf hc t
    (by linarith) hwt ht_locus.2
  exact (ne_of_gt hpositive) ht_locus.1

end BirkhoffGlobalSection

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc : 21 / 10 ≤ c) (s : BirkhoffGlobalSection.Phase)
    (hs : s ∈ BirkhoffGlobalSection.leftEnergyComponent μ c) :
    Real.sqrt (BirkhoffGlobalSection.wNormSq s) ≤ 2 :=
  BirkhoffGlobalSection.momentum_bound_proof μ c hμ0 hμhalf hc s hs
