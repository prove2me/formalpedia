-- Prove2me | solution 1 for DouglasVacua.flux_vacua_count_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:56:05.534747+00:00
-- url     : https://prove2.me/submissions/3f349b4b-f341-4c93-af0a-228c8049ed03

import Mathlib
import Definitions.Def_douglas_flux_vacua_count

open Real MeasureTheory Filter Topology

lemma dvSqrtPow (x : ℝ) (hx : 0 ≤ x) (J : ℕ) : Real.sqrt x ^ J = x ^ ((J : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

lemma dvFluxVolume (J : ℕ) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    volume {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
      ENNReal.ofReal (π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) *
        (V / c) ^ ((J : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    have hU : {x : Fin 0 → ℝ | c * ∑ i, x i ^ 2 ≤ V} = Set.univ := by
      ext x
      simp [hV]
    rw [hU, volume_pi, Measure.pi_univ]
    simp
  · have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
    have hVc : 0 ≤ V / c := div_nonneg hV hc.le
    set r := Real.sqrt (V / c) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hS : {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
        (WithLp.toLp 2) ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin J)) r) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff]
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hr0 two_ne_zero, EuclideanSpace.norm_sq_eq,
        hr, Real.sq_sqrt hVc, le_div_iff₀ hc, mul_comm]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hS, (PiLp.volume_preserving_toLp (Fin J)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall,
      Fintype.card_fin, ← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (pow_nonneg hr0 _)]
    congr 1
    rw [hr, dvSqrtPow _ hVc, dvSqrtPow _ Real.pi_pos.le]
    ring

abbrev dvLat (J : ℕ) : Submodule ℤ (Fin J → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin J)))

lemma dvLat_covolume (J : ℕ) : ZLattice.covolume (dvLat J) = 1 := by
  rw [ZLattice.covolume_eq_det (dvLat J) ((Pi.basisFun ℝ (Fin J)).restrictScalars ℤ)]
  have hM : Matrix.of ((↑) ∘ ((Pi.basisFun ℝ (Fin J)).restrictScalars ℤ)) =
      (1 : Matrix (Fin J) (Fin J) ℝ) := by
    ext i j
    simp [Module.Basis.restrictScalars_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hM, Matrix.det_one, abs_one]

lemma dvLat_mem (J : ℕ) (x : Fin J → ℝ) : x ∈ dvLat J ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
  rw [dvLat, (Pi.basisFun ℝ (Fin J)).mem_span_iff_repr_mem ℤ x]
  simp [Pi.basisFun_repr, Set.mem_range]

lemma dvF_iff (J : ℕ) (hJ : J ≠ 0) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) (x : Fin J → ℝ) :
    Real.sqrt (∑ i, x i ^ 2) ^ J ≤ Real.sqrt (V / c) ^ J ↔ c * ∑ i, x i ^ 2 ≤ V := by
  rw [pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hJ,
    Real.sqrt_le_sqrt_iff (div_nonneg hV hc.le), le_div_iff₀ hc, mul_comm]

lemma dvCount_eq (J : ℕ) (hJ : J ≠ 0) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    DouglasVacua.fluxVacuaCount J c V =
      Nat.card ↥({x : Fin J → ℝ | x ∈ Set.univ ∧
        Real.sqrt (∑ i, x i ^ 2) ^ J ≤ Real.sqrt (V / c) ^ J} ∩
          ((dvLat J : Submodule ℤ (Fin J → ℝ)) : Set (Fin J → ℝ))) := by
  have hinj : Function.Injective (fun (N : Fin J → ℤ) (i : Fin J) => (N i : ℝ)) := by
    intro a b h
    funext i
    have h' : ((a i : ℤ) : ℝ) = b i := congrFun h i
    exact_mod_cast h'
  rw [DouglasVacua.fluxVacuaCount, Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext x
  constructor
  · rintro ⟨N, hN, rfl⟩
    exact ⟨⟨Set.mem_univ _, (dvF_iff J hJ c V hc hV _).2 hN⟩,
      (dvLat_mem J _).2 fun i => ⟨N i, rfl⟩⟩
  · rintro ⟨⟨-, hx⟩, hL⟩
    choose N hN using (dvLat_mem J x).1 hL
    refine ⟨N, ?_, funext hN⟩
    show c * ∑ i, ((N i : ℝ)) ^ 2 ≤ V
    simp only [hN]
    exact (dvF_iff J hJ c V hc hV x).1 hx

lemma dvBall_eq (J : ℕ) (hJ : J ≠ 0) :
    {x : Fin J → ℝ | x ∈ Set.univ ∧ Real.sqrt (∑ i, x i ^ 2) ^ J ≤ 1} =
      {x : Fin J → ℝ | 1 * ∑ i, x i ^ 2 ≤ 1} := by
  ext x
  have h := dvF_iff J hJ 1 1 one_pos zero_le_one x
  have h1 : Real.sqrt (1 / 1) ^ J = 1 := by simp
  rw [h1] at h
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and]
  exact h

lemma dvSphere_null (J : ℕ) :
    volume {x : Fin J → ℝ | 1 * ∑ i, x i ^ 2 = 1} = 0 := by
  have hS : {x : Fin J → ℝ | 1 * ∑ i, x i ^ 2 = 1} =
      (WithLp.toLp 2) ⁻¹' (Metric.sphere (0 : EuclideanSpace ℝ (Fin J)) 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_sphere_zero_iff_norm, one_mul]
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hS, (PiLp.volume_preserving_toLp (Fin J)).measure_preimage
    Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
  exact Measure.addHaar_sphere_of_ne_zero volume 0 one_ne_zero

open Real Filter Topology DouglasVacua in
theorem solution (J : ℕ) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun V : ℝ => (fluxVacuaCount J c V : ℝ) / (V / c) ^ ((J : ℝ) / 2)) atTop
      (𝓝 (π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1))) := by
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · subst hJ0
    have hone : ∀ V : ℝ, 0 ≤ V → fluxVacuaCount 0 c V = 1 := by
      intro V hV
      have hU : {N : Fin 0 → ℤ | fluxPotential c N ≤ V} = Set.univ := by
        ext N
        simp [fluxPotential, hV]
      rw [fluxVacuaCount, hU, Set.ncard_univ, Nat.card_unique]
    simp only [Nat.cast_zero, zero_div, Real.rpow_zero, zero_add, Real.Gamma_one, div_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with V hV
    rw [hone V hV, Nat.cast_one]
  · have hJ : J ≠ 0 := hJpos.ne'
    have : Nonempty (Fin J) := ⟨⟨0, hJpos⟩⟩
    have hX : ∀ ⦃x : Fin J → ℝ⦄ ⦃r : ℝ⦄, x ∈ (Set.univ : Set (Fin J → ℝ)) → 0 < r →
        r • x ∈ (Set.univ : Set (Fin J → ℝ)) := fun _ _ _ _ => Set.mem_univ _
    have h₁ : ∀ (x : Fin J → ℝ) ⦃r : ℝ⦄, 0 ≤ r →
        (fun y : Fin J → ℝ => Real.sqrt (∑ i, y i ^ 2) ^ J) (r • x) =
          r ^ Fintype.card (Fin J) * (fun y : Fin J → ℝ => Real.sqrt (∑ i, y i ^ 2) ^ J) x := by
      intro x r hr
      have hs : ∑ i, (r * x i) ^ 2 = r ^ 2 * ∑ i, x i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      simp only [Pi.smul_apply, smul_eq_mul, Fintype.card_fin]
      rw [hs, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr, mul_pow]
    have h₂ : Bornology.IsBounded {x : Fin J → ℝ | x ∈ Set.univ ∧
        (fun y : Fin J → ℝ => Real.sqrt (∑ i, y i ^ 2) ^ J) x ≤ 1} := by
      simp only
      rw [dvBall_eq J hJ]
      refine (Metric.isBounded_closedBall (x := (0 : Fin J → ℝ)) (r := 1)).subset ?_
      intro x hx
      have hx' : ∑ j, x j ^ 2 ≤ 1 := by simpa using hx
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
        Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
      exact hi.trans hx'
    have hmeasB : MeasurableSet {x : Fin J → ℝ | 1 * ∑ i, x i ^ 2 ≤ 1} :=
      measurableSet_le (by fun_prop) measurable_const
    have h₃ : MeasurableSet {x : Fin J → ℝ | x ∈ Set.univ ∧
        (fun y : Fin J → ℝ => Real.sqrt (∑ i, y i ^ 2) ^ J) x ≤ 1} := by
      simp only
      rw [dvBall_eq J hJ]
      exact hmeasB
    have h₄ : volume (frontier {x : Fin J → ℝ | x ∈ Set.univ ∧
        (fun y : Fin J → ℝ => Real.sqrt (∑ i, y i ^ 2) ^ J) x ≤ 1}) = 0 := by
      simp only
      rw [dvBall_eq J hJ]
      refine measure_mono_null (frontier_le_subset_eq
        (f := fun x : Fin J → ℝ => 1 * ∑ i, x i ^ 2) (g := fun _ => (1 : ℝ))
        (by fun_prop) continuous_const) ?_
      exact dvSphere_null J
    have hlim := ZLattice.covolume.tendsto_card_le_div (dvLat J) hX h₁ h₂ h₃ h₄
    have hval : volume.real {x : Fin J → ℝ | x ∈ Set.univ ∧
        (fun y : Fin J → ℝ => Real.sqrt (∑ i, y i ^ 2) ^ J) x ≤ 1} /
          ZLattice.covolume (dvLat J) =
        π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) := by
      simp only
      rw [dvBall_eq J hJ, dvLat_covolume, div_one, measureReal_def,
        dvFluxVolume J 1 1 one_pos zero_le_one, ENNReal.toReal_ofReal]
      · simp
      · exact mul_nonneg (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
          (Real.Gamma_pos_of_pos (by positivity)).le) (Real.rpow_nonneg (by norm_num) _)
    rw [hval] at hlim
    have hVc : Tendsto (fun V : ℝ => V / c) atTop atTop := tendsto_id.atTop_div_const hc
    have hT : Tendsto (fun V : ℝ => Real.sqrt (V / c) ^ J) atTop atTop :=
      (tendsto_pow_atTop hJ).comp (Real.tendsto_sqrt_atTop.comp hVc)
    refine (hlim.comp hT).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with V hV
    simp only [Function.comp_apply]
    rw [← dvCount_eq J hJ c V hc hV, dvSqrtPow (V / c) (div_nonneg hV hc.le) J]

