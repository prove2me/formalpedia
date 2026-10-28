-- Prove2me | solution 1 for CondPortOT.BigRadius.exists_measure_condExp_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:23:27.978905+00:00
-- url     : https://prove2.me/submissions/d73cae46-3af2-452d-9b0b-3b6326c79f36

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ < ENNReal.ofReal ρ) (L : Y → ℝ) (y0 : Y) :
    ∃ Q : Measure (X × Y), CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧ 0 < Q (CondPortOT.SingUninf.fiber DX x0 γ) ∧
      CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 γ) L = (L y0 : EReal) := by
  classical
  set S := CondPortOT.SingUninf.fiber (Y := Y) DX x0 γ with hS
  set c := CondPortOT.SingUninf.groundCost DX DY with hc
  set P := CondPortOT.SingUninf.empirical xh yh with hP
  -- a measure with no fiber mass and transport cost below ρ
  obtain ⟨Q₁, hQ₁, hQ₁c⟩ : ∃ Q₁ : Measure (X × Y), (IsProbabilityMeasure Q₁ ∧ Q₁ S = 0) ∧
      transportCost c Q₁ P < ENNReal.ofReal ρ := by
    have := hρ
    unfold CondPortOT.BigRadius.rhoMax at this
    simp only [iInf_lt_iff] at this
    obtain ⟨Q₁, h1, h2⟩ := this
    exact ⟨Q₁, h1, h2⟩
  obtain ⟨π₁, hπ₁, hπ₁c⟩ : ∃ π₁ : Measure ((X × Y) × (X × Y)),
      (IsProbabilityMeasure π₁ ∧ π₁.map Prod.fst = Q₁ ∧ π₁.map Prod.snd = P) ∧
      ∫⁻ w, c w.1 w.2 ∂π₁ < ENNReal.ofReal ρ := by
    have := hQ₁c
    unfold transportCost at this
    simp only [iInf_lt_iff] at this
    obtain ⟨π₁, h1, h2⟩ := this
    exact ⟨π₁, h1, h2⟩
  set a := ∫⁻ w, c w.1 w.2 ∂π₁ with ha
  have ha_top : a ≠ ⊤ := ne_top_of_lt hπ₁c
  -- the point (x0, y0) lies in the fiber
  have hx0 : (x0, y0) ∈ S := by
    have h0 : DX x0 x0 + DY y0 y0 = 0 := (hA.eq_zero_iff x0 x0 y0 y0).2 rfl
    have := hA.nonnegY y0 y0
    show DX x0 x0 ≤ γ ∧ y0 ∈ Set.univ
    exact ⟨by linarith, trivial⟩
  -- the transport plan for the point mass
  set π₂ : Measure ((X × Y) × (X × Y)) :=
    (N : ENNReal)⁻¹ • ∑ i, Measure.dirac ((x0, y0), (xh i, yh i)) with hπ₂
  set C : ℝ := (N : ℝ)⁻¹ * ∑ i, (DX x0 (xh i) + DY y0 (yh i)) with hCdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hC0 : 0 ≤ C := by
    apply mul_nonneg (inv_nonneg.2 hNpos.le)
    exact Finset.sum_nonneg (fun i _ => add_nonneg (hA.nonnegX _ _) (hA.nonnegY _ _))
  have hπ₂c : ∫⁻ w, c w.1 w.2 ∂π₂ = ENNReal.ofReal C := by
    rw [hπ₂, lintegral_smul_measure, lintegral_finsetSum_measure]
    simp only [lintegral_dirac]
    rw [hc]
    simp only [CondPortOT.SingUninf.groundCost]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => add_nonneg (hA.nonnegX _ _) (hA.nonnegY _ _))]
    rw [hCdef, ENNReal.ofReal_mul (inv_nonneg.2 hNpos.le), ENNReal.ofReal_inv_of_pos hNpos]
    simp
  have hNe : (N : ENNReal) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hπ₂fst : π₂.map Prod.fst = Measure.dirac (x0, y0) := by
    rw [hπ₂, Measure.map_smul, Measure.map_finset_sum measurable_fst.aemeasurable]
    simp only [Measure.map_dirac' measurable_fst]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ENNReal,
      smul_smul, ENNReal.inv_mul_cancel hNe hNt, one_smul]
  have hπ₂snd : π₂.map Prod.snd = P := by
    rw [hπ₂, Measure.map_smul, Measure.map_finset_sum measurable_snd.aemeasurable]
    simp only [Measure.map_dirac' measurable_snd]
    rfl
  -- choose the mixing weight
  set a' := a.toReal with ha'
  have ha'0 : 0 ≤ a' := ENNReal.toReal_nonneg
  have hρa : a' < ρ := by
    have := (ENNReal.toReal_lt_toReal ha_top ENNReal.ofReal_ne_top).2 hπ₁c
    have hρ0 : 0 ≤ ρ := by
      by_contra h
      push_neg at h
      rw [ENNReal.ofReal_of_nonpos h.le] at hπ₁c
      exact absurd hπ₁c (not_lt_zero')
    rwa [ENNReal.toReal_ofReal hρ0] at this
  set t : ℝ := min (1 / 2) ((ρ - a') / (C + 1)) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htC : t * C ≤ ρ - a' := by
    have h1 : t ≤ (ρ - a') / (C + 1) := min_le_right _ _
    have h2 : t * (C + 1) ≤ ρ - a' := by
      rwa [le_div_iff₀ (by linarith)] at h1
    nlinarith
  set s₁ := ENNReal.ofReal (1 - t)
  set s₂ := ENNReal.ofReal t
  have hs : s₁ + s₂ = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) ht0.le]; simp
  set Q : Measure (X × Y) := s₁ • Q₁ + s₂ • Measure.dirac (x0, y0) with hQ
  have hQ₁S : Q₁.restrict S = 0 := Measure.restrict_eq_zero.2 hQ₁.2
  have hQS : Q S = s₂ := by
    rw [hQ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hQ₁.2,
      Measure.dirac_apply_of_mem hx0]
    simp
  have hQres : Q.restrict S = s₂ • Measure.dirac (x0, y0) := by
    rw [hQ, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, hQ₁S,
      MeasureTheory.restrict_dirac, if_pos hx0]
    simp
  haveI := hQ₁.1
  refine ⟨Q, ⟨?_, ?_⟩, ?_, ?_⟩
  · constructor
    rw [hQ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ]
    simpa using hs
  · -- transport cost bound
    unfold transportCost
    refine iInf₂_le_of_le (s₁ • π₁ + s₂ • π₂) ⟨?_, ?_, ?_⟩ ?_
    · haveI := hπ₁.1
      constructor
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ]
      have : π₂ Set.univ = 1 := by
        rw [show π₂ Set.univ = (π₂.map Prod.fst) Set.univ by
          rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl, hπ₂fst]; simp
      rw [this]; simpa using hs
    · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, hπ₁.2.1,
        hπ₂fst]
    · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, hπ₁.2.2,
        hπ₂snd, ← add_smul, hs, one_smul]
    · rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, ← ha, hπ₂c]
      simp only [smul_eq_mul]
      rw [← ENNReal.ofReal_toReal ha_top, ← ha', ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_mul ht0.le, ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
  · rw [hQS]; exact ENNReal.ofReal_pos.2 ht0
  · unfold CondPortOT.SingUninf.condExp extIntegral
    rw [hQS, hQres, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
      lintegral_dirac]
    simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal ht0.le, ← ENNReal.ofReal_mul ht0.le, ← ENNReal.ofReal_mul ht0.le,
      EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal]
    have key : (t⁻¹ : ℝ) * (max (t * L y0) 0 - max (t * -L y0) 0) = L y0 := by
      rcases le_total 0 (L y0) with h | h
      · rw [max_eq_left (mul_nonneg ht0.le h), max_eq_right (by nlinarith), sub_zero,
          ← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul]
      · rw [max_eq_right (by nlinarith), max_eq_left (by nlinarith), zero_sub]
        have : t⁻¹ * t = 1 := inv_mul_cancel₀ ht0.ne'
        linear_combination (L y0) * this
    calc ((t⁻¹ : ℝ) : EReal) * (((max (t * L y0) 0 : ℝ) : EReal) - ((max (t * -L y0) 0 : ℝ) : EReal))
        = (((t⁻¹ : ℝ) * (max (t * L y0) 0 - max (t * -L y0) 0) : ℝ) : EReal) := by
          rw [EReal.coe_mul, EReal.coe_sub]
      _ = (L y0 : EReal) := by rw [key]
