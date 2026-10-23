-- Prove2me | solution 1 for DRMeanVar.Reform.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:55:16.41525+00:00
-- url     : https://prove2.me/submissions/a443f63e-141a-4d9b-9ec2-5818bfc2f126

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory


namespace DRMVAux

theorem holder_dot {d : ℕ} (p q : ENNReal) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ Δ : Fin d → ℝ) :
    |φ ⬝ᵥ Δ| ≤ ‖WithLp.toLp p φ‖ * ‖WithLp.toLp q Δ‖ := by
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  haveI : Fact (1 ≤ q) := ⟨hq⟩
  have h1 : |φ ⬝ᵥ Δ| ≤ ∑ i, |φ i| * |Δ i| := by
    unfold dotProduct
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    simp [abs_mul]
  by_cases hq1 : q = 1
  · subst hq1
    have hp : p = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).2 rfl
    subst hp
    rw [PiLp.norm_eq_of_L1]
    refine h1.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : |φ i| ≤ ‖WithLp.toLp ⊤ φ‖ := by
      have := PiLp.norm_apply_le (WithLp.toLp ⊤ φ) i
      simpa [Real.norm_eq_abs] using this
    simp only [PiLp.toLp_apply, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  · have hptop : p ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p q).2 hq1
    have hR := ENNReal.HolderConjugate.toReal_of_ne_top hptop hqtop (p := p) (q := q)
    have hp0 : 0 < p.toReal := hR.pos
    have hq0 : 0 < q.toReal := hR.symm.pos
    rw [PiLp.norm_eq_sum hp0, PiLp.norm_eq_sum hq0]
    refine h1.trans ?_
    have := Real.inner_le_Lp_mul_Lq (s := Finset.univ) (f := fun i => |φ i|) (g := fun i => |Δ i|) hR
    simpa [Real.norm_eq_abs] using this

theorem dual_attain {d : ℕ} (p q : ENNReal) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) :
    ∃ u : Fin d → ℝ, ‖WithLp.toLp q u‖ ≤ 1 ∧ φ ⬝ᵥ u = ‖WithLp.toLp p φ‖ := by
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  haveI : Fact (1 ≤ q) := ⟨hq⟩
  by_cases hq1 : q = 1
  · subst hq1
    have hp : p = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).2 rfl
    subst hp
    rw [PiLp.norm_toLp]
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · refine ⟨0, by simp, ?_⟩
      simp [Subsingleton.elim φ 0]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
        Finset.univ_nonempty (fun j => ‖φ j‖₊)
      have hnorm : ‖φ‖ = |φ i| := by
        rw [← coe_nnnorm, Pi.nnnorm_def, hi]; simp [Real.norm_eq_abs]
      refine ⟨Pi.single i (SignType.sign (φ i) : ℝ), ?_, ?_⟩
      · rw [PiLp.norm_toLp_single]
        rcases lt_trichotomy (φ i) 0 with h | h | h <;> simp [h]
      · rw [hnorm, dotProduct_single]
        rcases lt_trichotomy (φ i) 0 with h | h | h <;> simp [h, abs_of_neg, abs_of_pos]
  · have hptop : p ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one p q).2 hq1
    have hR := ENNReal.HolderConjugate.toReal_of_ne_top hptop hqtop (p := p) (q := q)
    have hp0 : 0 < p.toReal := hR.pos
    have hq0 : 0 < q.toReal := hR.symm.pos
    obtain ⟨⟨g, hg, hfg⟩, -⟩ := NNReal.isGreatest_Lp Finset.univ (fun i => ‖φ i‖₊) hR
    simp only [Set.mem_setOf_eq] at hg
    refine ⟨fun i => (SignType.sign (φ i) : ℝ) * g i, ?_, ?_⟩
    · rw [PiLp.norm_eq_sum hq0]
      have hle : ∑ i, ‖(SignType.sign (φ i) : ℝ) * g i‖ ^ q.toReal ≤ ∑ i, ((g i : ℝ)) ^ q.toReal := by
        refine Finset.sum_le_sum fun i _ => ?_
        apply Real.rpow_le_rpow (norm_nonneg _) _ hq0.le
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        have : |(SignType.sign (φ i) : ℝ)| ≤ 1 := by
          rcases lt_trichotomy (φ i) 0 with h | h | h <;> simp [h]
        nlinarith [NNReal.coe_nonneg (g i), abs_nonneg ((SignType.sign (φ i) : ℝ))]
      have hg' : ∑ i, ((g i : ℝ)) ^ q.toReal ≤ 1 := by exact_mod_cast hg
      simp only [PiLp.toLp_apply]
      calc _ ≤ (1:ℝ) ^ (1 / q.toReal) := by
            apply Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) (hle.trans hg')
              (by positivity)
        _ = 1 := Real.one_rpow _
    · rw [PiLp.norm_eq_sum hp0]
      have := congrArg (fun x : NNReal => (x : ℝ)) hfg
      simp only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, NNReal.coe_rpow,
        Real.norm_eq_abs] at this
      simp only [PiLp.toLp_apply, Real.norm_eq_abs]
      rw [← this]
      unfold dotProduct
      refine Finset.sum_congr rfl fun i _ => ?_
      rcases lt_trichotomy (φ i) 0 with h | h | h <;> simp [h, abs_of_neg, abs_of_pos] <;> ring

noncomputable def avgDirac {X ι : Type*} [MeasurableSpace X] [Fintype ι] (x : ι → X) : Measure X :=
  ((Fintype.card ι : ENNReal))⁻¹ • ∑ i, Measure.dirac (x i)

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype ι]

theorem avgDirac_isProb [Nonempty ι] (x : ι → X) : IsProbabilityMeasure (avgDirac x) := by
  constructor
  have hn : (Fintype.card ι : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [avgDirac, Measure.coe_finsetSum, Finset.sum_apply]
  exact ENNReal.inv_mul_cancel hn (ENNReal.natCast_ne_top _)

theorem map_avgDirac (x : ι → X) {g : X → Y} (hg : Measurable g) :
    (avgDirac x).map g = avgDirac (g ∘ x) := by
  ext s hs
  rw [Measure.map_apply hg hs]
  simp only [avgDirac, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul,
    Function.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.dirac_apply' _ (hg hs), Measure.dirac_apply' _ hs]
  by_cases h : g (x i) ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

theorem lintegral_avgDirac [MeasurableSingletonClass X] (x : ι → X) (f : X → ENNReal) :
    ∫⁻ y, f y ∂(avgDirac x) = (Fintype.card ι : ENNReal)⁻¹ * ∑ i, f (x i) := by
  simp [avgDirac, lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac]

theorem integrable_avgDirac [MeasurableSingletonClass X] [Nonempty ι] (x : ι → X) (f : X → ℝ) :
    Integrable f (avgDirac x) := by
  unfold avgDirac
  refine Integrable.smul_measure ?_ (by simp)
  exact integrable_finsetSum_measure.2 fun i _ => integrable_dirac (by simp)

theorem integral_avgDirac [MeasurableSingletonClass X] [Nonempty ι] (x : ι → X) (f : X → ℝ) :
    ∫ y, f y ∂(avgDirac x) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (x i) := by
  unfold avgDirac
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, smul_eq_mul, ENNReal.toReal_inv]
  · intro i _; exact integrable_dirac (by simp)

theorem avgDirac_fst_bool (x : ι → X) :
    avgDirac (fun j : ι × Bool => x j.1) = avgDirac x := by
  unfold avgDirac
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool]
  rw [← Finset.sum_add_distrib.symm.trans rfl]
  simp only [← two_smul ENNReal, smul_smul]
  congr 1
  push_cast
  rw [ENNReal.mul_inv (by simp) (by simp), mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one]

end DRMVAux


open MeasureTheory

namespace DRMeanVar.Reform
open DRMVAux

theorem empVar_eq_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    empVar R φ = empSecond R φ - (empMean R φ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  unfold empVar empSecond
  have hm : ∑ i, φ ⬝ᵥ R i = n * empMean R φ := by
    unfold empMean; field_simp
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem empVar_nonneg_aux {d n : ℕ} (R : Fin n → (Fin d → ℝ)) (φ : Fin d → ℝ) :
    0 ≤ empVar R φ := by
  unfold empVar
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem Pn_eq_avgDirac {d n : ℕ} (R : Fin n → (Fin d → ℝ)) : Pn R = avgDirac R := by
  simp [Pn, avgDirac]

theorem sum_bool_split {n : ℕ} (f : Fin n × Bool → ℝ) :
    ∑ j, f j = ∑ i, (f (i, true) + f (i, false)) := by
  rw [Fintype.sum_prod_type]; simp [Fintype.sum_bool]

theorem sumL1 {n : ℕ} (Y : Fin n → ℝ) (A B : ℝ) :
    ∑ i, (A + B * Y i) = n * A + B * ∑ i, Y i := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem sumL2 {n : ℕ} (Y : Fin n → ℝ) (A B : ℝ) :
    ∑ i, (A + B * Y i) ^ 2 = n * A ^ 2 + 2 * A * B * ∑ i, Y i + B ^ 2 * ∑ i, Y i ^ 2 := by
  simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_pow]
  congr 1
  · congr 1; refine Finset.sum_congr rfl fun i _ => by ring

theorem attain_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ α : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    ∃ P ∈ U q δ R, pMean P φ = α ∧ pSecond P φ = hFun p δ R α φ := by
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  haveI : Fact (1 ≤ q) := ⟨hq⟩
  obtain ⟨u, hu1, hu⟩ := dual_attain p q hq hqtop hpq φ
  set N := ‖WithLp.toLp p φ‖ with hNdef
  have hN : 0 ≤ N := norm_nonneg _
  set m := empMean R φ with hmdef
  set V := empVar R φ with hVdef
  set S := empSecond R φ with hSdef
  set C := α - m with hCdef
  set D := δ * N ^ 2 - C ^ 2 with hDdef
  have hD : 0 ≤ D := by linarith
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := by positivity
  set Y : Fin n → ℝ := fun i => φ ⬝ᵥ R i with hYdef
  have hsumY : ∑ i, Y i = n * m := by
    simp only [hmdef, empMean, hYdef]; field_simp
  have hsumY2 : ∑ i, Y i ^ 2 = n * S := by
    simp only [hSdef, empSecond, hYdef]; field_simp
  have hV0 : 0 ≤ V := by
    simp only [hVdef, empVar]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsumA2 : ∑ i, (Y i - m) ^ 2 = n * V := by
    simp only [hVdef, empVar, hYdef, hmdef]; field_simp
  have hVS : V = S - m ^ 2 := by
    have h2 : ∑ i, (Y i - m) ^ 2 = n * (-m) ^ 2 + 2 * (-m) * 1 * ∑ i, Y i + 1 ^ 2 * ∑ i, Y i ^ 2 := by
      rw [← sumL2]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsumA2, hsumY2, hsumY] at h2
    have : n * V = n * (S - m ^ 2) := by linarith
    exact mul_left_cancel₀ hn this
  -- the parameters k and r
  set k : ℝ := if V = 0 then 0 else Real.sqrt D / Real.sqrt V with hkdef
  set r : ℝ := Real.sqrt (D - k ^ 2 * V) with hrdef
  have hkV : k * V = Real.sqrt D * Real.sqrt V := by
    by_cases hV : V = 0
    · simp [hkdef, hV]
    · have hsV : Real.sqrt V ≠ 0 := by
        rw [Real.sqrt_ne_zero hV0]; exact hV
      simp only [hkdef, hV, if_false]
      field_simp
      rw [Real.sq_sqrt hV0]
  have hk2 : k ^ 2 * V ≤ D := by
    by_cases hV : V = 0
    · simp [hkdef, hV, hD]
    · have hsV : Real.sqrt V ≠ 0 := by
        rw [Real.sqrt_ne_zero hV0]; exact hV
      simp only [hkdef, hV, if_false]
      rw [div_pow, Real.sq_sqrt hD, Real.sq_sqrt hV0]
      field_simp
      exact le_refl _
  have hr2 : r ^ 2 = D - k ^ 2 * V := Real.sq_sqrt (by linarith)
  -- the perturbations
  set z : Fin n × Bool → ℝ := fun j => C + k * (Y j.1 - m) + (if j.2 then r else -r) with hzdef
  set a : Fin n × Bool → (Fin d → ℝ) := fun j => (z j / N) • u with hadef
  have hza : ∀ j, φ ⬝ᵥ a j = z j := by
    intro j
    simp only [hadef, dotProduct_smul, hu, smul_eq_mul]
    by_cases hN0 : N = 0
    · have hC : C = 0 := by
        have : C ^ 2 ≤ 0 := by
          have := hD; simp only [hDdef, hN0] at this; nlinarith [this]
        nlinarith [sq_nonneg C]
      have hD0 : D = 0 := by simp [hDdef, hN0, hC]
      have hk0 : k = 0 := by simp [hkdef, hD0]
      have hr0 : r = 0 := by simp [hrdef, hD0, hk0]
      simp [hzdef, hC, hk0, hr0, hN0]
    · field_simp
  set x : Fin n × Bool → (Fin d → ℝ) := fun j => R j.1 + a j with hxdef
  refine ⟨avgDirac x, ⟨avgDirac_isProb x, ?_⟩, ?_, ?_⟩
  · -- transport cost
    unfold RWPI.SqrtLasso.transportCost
    refine le_trans (iInf₂_le (avgDirac (fun j => (x j, R j.1))) ?_) ?_
    · refine ⟨avgDirac_isProb _, ?_, ?_⟩
      · rw [map_avgDirac _ measurable_fst]; rfl
      · rw [map_avgDirac _ measurable_snd, Pn_eq_avgDirac]
        exact avgDirac_fst_bool R
    · rw [lintegral_avgDirac]
      have hterm : ∀ j, lqSqCost q (x j) (R j.1) ≤
          ENNReal.ofReal ((z j / N) ^ 2) := by
        intro j
        simp only [lqSqCost, hxdef, sub_add_cancel_left, WithLp.toLp_neg, norm_neg]
        apply ENNReal.ofReal_le_ofReal
        simp only [hadef, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
        rw [mul_pow, sq_abs]
        have h0 : ‖WithLp.toLp q u‖ ^ 2 ≤ 1 := by
          have := norm_nonneg (WithLp.toLp q u); nlinarith
        nlinarith [sq_nonneg (z j / N)]
      calc _ ≤ ((Fintype.card (Fin n × Bool) : ENNReal))⁻¹ *
            ∑ j, ENNReal.ofReal ((z j / N) ^ 2) := by
            exact mul_le_mul_right (Finset.sum_le_sum fun j _ => hterm j) _
        _ = ENNReal.ofReal ((Fintype.card (Fin n × Bool) : ℝ)⁻¹ * ∑ j, (z j / N) ^ 2) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
              (fun j _ => sq_nonneg _), ENNReal.ofReal_inv_of_pos (by positivity)]
            simp only [ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal δ := by
            apply ENNReal.ofReal_le_ofReal
            simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, div_pow,
              ← Finset.sum_div]
            rw [sum_bool_split]
            simp only [hzdef, if_true, Bool.false_eq_true, if_false]
            have hexp : ∑ i, ((C + k * (Y i - m) + r) ^ 2 + (C + k * (Y i - m) + -r) ^ 2) =
                ∑ i, (2 * (C - k * m) ^ 2 + 2 * r ^ 2 + 4 * (C - k * m) * k * Y i
                  + 2 * k ^ 2 * Y i ^ 2) := Finset.sum_congr rfl fun i _ => by ring
            have hsplit : ∑ i, (2 * (C - k * m) ^ 2 + 2 * r ^ 2 + 4 * (C - k * m) * k * Y i
                  + 2 * k ^ 2 * Y i ^ 2) = n * (2 * (C - k * m) ^ 2 + 2 * r ^ 2) +
                  4 * (C - k * m) * k * ∑ i, Y i + 2 * k ^ 2 * ∑ i, Y i ^ 2 := by
              simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
                Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
            rw [hexp, hsplit, hsumY, hsumY2, hr2]
            by_cases hN0 : N = 0
            · simp [hN0]; exact hδ
            · have hN2 : 0 < N ^ 2 := by positivity
              have : (↑(n * 2) : ℝ)⁻¹ * (↑n * (2 * (C - k * m) ^ 2 + 2 * (D - k ^ 2 * V)) +
                  4 * (C - k * m) * k * (↑n * m) + 2 * k ^ 2 * (↑n * S)) = C ^ 2 + D := by
                push_cast; field_simp; rw [hVS]; ring
              rw [← mul_div_assoc, this, div_le_iff₀ hN2, hDdef]
              linarith
  · unfold pMean
    rw [integral_avgDirac]
    simp only [hxdef, dotProduct_add, hza, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [sum_bool_split]
    simp only [hzdef, if_true, Bool.false_eq_true, if_false]
    have hexp : ∑ i, ((φ ⬝ᵥ R i + (C + k * (Y i - m) + r)) + (φ ⬝ᵥ R i + (C + k * (Y i - m) + -r)))
        = ∑ i, (2 * (C - k * m) + (2 + 2 * k) * Y i) :=
      Finset.sum_congr rfl fun i _ => by simp only [hYdef]; ring
    rw [hexp, sumL1, hsumY]
    push_cast
    field_simp
    simp only [hCdef]; ring
  · unfold pSecond
    rw [integral_avgDirac]
    simp only [hxdef, dotProduct_add, hza, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [sum_bool_split]
    simp only [hzdef, if_true, Bool.false_eq_true, if_false]
    have hexp : ∑ i, ((φ ⬝ᵥ R i + (C + k * (Y i - m) + r)) ^ 2 +
        (φ ⬝ᵥ R i + (C + k * (Y i - m) + -r)) ^ 2)
        = ∑ i, ((2 * (C - k * m) ^ 2 + 2 * r ^ 2) + (4 * (C - k * m) * (1 + k)) * Y i
          + (2 * (1 + k) ^ 2) * Y i ^ 2) :=
      Finset.sum_congr rfl fun i _ => by simp only [hYdef]; ring
    have hsplit : ∑ i, ((2 * (C - k * m) ^ 2 + 2 * r ^ 2) + (4 * (C - k * m) * (1 + k)) * Y i
          + (2 * (1 + k) ^ 2) * Y i ^ 2) = n * (2 * (C - k * m) ^ 2 + 2 * r ^ 2) +
          4 * (C - k * m) * (1 + k) * ∑ i, Y i + 2 * (1 + k) ^ 2 * ∑ i, Y i ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hexp, hsplit, hsumY, hsumY2, hr2]
    have hh : hFun p δ R α φ = S + 2 * C * m + δ * N ^ 2 + 2 * Real.sqrt D * Real.sqrt V := by
      simp only [hFun, hSdef, hCdef, hmdef, hNdef, hDdef, hVdef]
    rw [hh, mul_assoc 2 (Real.sqrt D), ← hkV]
    have hδN : δ * N ^ 2 = D + C ^ 2 := by simp only [hDdef]; ring
    rw [hδN, hVS]
    push_cast
    field_simp
    ring

end DRMeanVar.Reform


open MeasureTheory

namespace DRMeanVar.Reform
open DRMVAux

theorem int_lin {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} [IsProbabilityMeasure π]
    {f1 f2 f3 f4 f5 : Ω → ℝ} (h1 : Integrable f1 π) (h2 : Integrable f2 π) (h3 : Integrable f3 π)
    (h4 : Integrable f4 π) (h5 : Integrable f5 π) (a0 a1 a2 a3 a4 a5 : ℝ) :
    ∫ w, (a0 + a1 * f1 w + a2 * f2 w + a3 * f3 w + a4 * f4 w + a5 * f5 w) ∂π =
      a0 + a1 * ∫ w, f1 w ∂π + a2 * ∫ w, f2 w ∂π + a3 * ∫ w, f3 w ∂π + a4 * ∫ w, f4 w ∂π
        + a5 * ∫ w, f5 w ∂π := by
  have i0 : Integrable (fun _ : Ω => a0) π := integrable_const a0
  have i1 : Integrable (fun w => a0 + a1 * f1 w) π := i0.add (h1.const_mul a1)
  have i2 : Integrable (fun w => a0 + a1 * f1 w + a2 * f2 w) π := i1.add (h2.const_mul a2)
  have i3 : Integrable (fun w => a0 + a1 * f1 w + a2 * f2 w + a3 * f3 w) π :=
    i2.add (h3.const_mul a3)
  have i4 : Integrable (fun w => a0 + a1 * f1 w + a2 * f2 w + a3 * f3 w + a4 * f4 w) π :=
    i3.add (h4.const_mul a4)
  rw [integral_add i4 (h5.const_mul a5), integral_add i3 (h4.const_mul a4),
    integral_add i2 (h3.const_mul a3), integral_add i1 (h2.const_mul a2),
    integral_add i0 (h1.const_mul a1)]
  simp [integral_const_mul]

theorem upper_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) (P : Measure (Fin d → ℝ)) (hP : P ∈ U q δ R)
    (t : ℝ) (ht : δ < t) :
    ∃ T : ℝ, (pMean P φ - empMean R φ) ^ 2 ≤ T ∧ T ≤ ‖WithLp.toLp p φ‖ ^ 2 * t ∧
      pSecond P φ ≤ empSecond R φ + 2 * empMean R φ * (pMean P φ - empMean R φ) + T +
        2 * Real.sqrt (empVar R φ) * Real.sqrt (T - (pMean P φ - empMean R φ) ^ 2) := by
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  haveI : Fact (1 ≤ q) := ⟨hq⟩
  have ht0 : 0 < t := lt_of_le_of_lt hδ ht
  obtain ⟨hPprob, hcost⟩ := hP
  have hlt : RWPI.SqrtLasso.transportCost (lqSqCost q) P (Pn R) < ENNReal.ofReal t :=
    lt_of_le_of_lt hcost ((ENNReal.ofReal_lt_ofReal_iff ht0).2 ht)
  unfold RWPI.SqrtLasso.transportCost at hlt
  obtain ⟨π, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨⟨hπ, h1, h2⟩, hc⟩ := iInf_lt_iff.1 hlt
  set N := ‖WithLp.toLp p φ‖ with hNdef
  set m := empMean R φ with hmdef
  set V := empVar R φ with hVdef
  set S := empSecond R φ with hSdef
  -- basic functions
  set L : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun w => ‖WithLp.toLp q (w.1 - w.2)‖ with hLdef
  set Y : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun w => φ ⬝ᵥ w.2 with hYdef
  set Z : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun w => φ ⬝ᵥ (w.1 - w.2) with hZdef
  have hdotc : Continuous (fun x : Fin d → ℝ => φ ⬝ᵥ x) := by
    simp only [dotProduct]; fun_prop
  have hLc : Continuous L :=
    ((PiLp.continuous_toLp q _).comp (continuous_fst.sub continuous_snd)).norm
  have hYc : Continuous Y := hdotc.comp continuous_snd
  have hZc : Continuous Z := hdotc.comp (continuous_fst.sub continuous_snd)
  have hcostL : ∀ w : (Fin d → ℝ) × (Fin d → ℝ), lqSqCost q w.1 w.2 = ENNReal.ofReal (L w ^ 2) := by
    intro w
    simp only [lqSqCost, hLdef]
    rw [← neg_sub, WithLp.toLp_neg, norm_neg]
  simp only [hcostL] at hc
  have hL2 : Integrable (fun w => L w ^ 2) π := by
    rw [← lintegral_ofReal_ne_top_iff_integrable (f := fun w => L w ^ 2)
      ((hLc.pow 2).aestronglyMeasurable)
      (ae_of_all _ fun w => sq_nonneg _)]
    exact (lt_of_lt_of_le hc le_top).ne
  have hEL2 : ∫ w, L w ^ 2 ∂π ≤ t := by
    have := ofReal_integral_eq_lintegral_ofReal hL2 (ae_of_all _ fun w => sq_nonneg (L w))
    rw [← this] at hc
    exact ((ENNReal.ofReal_lt_ofReal_iff ht0).1 hc).le
  -- functions of the second coordinate
  have hsnd : ∀ g : (Fin d → ℝ) → ℝ, Continuous g →
      Integrable (fun w => g w.2) π ∧ ∫ w, g w.2 ∂π = (n : ℝ)⁻¹ * ∑ i, g (R i) := by
    intro g hg
    have hmap : π.map Prod.snd = avgDirac R := by rw [h2, Pn_eq_avgDirac]
    constructor
    · have := (integrable_map_measure (μ := π) (f := Prod.snd) (g := g)
        hg.aestronglyMeasurable measurable_snd.aemeasurable).1 (by rw [hmap]; exact integrable_avgDirac R g)
      exact this
    · rw [← integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable, hmap,
        integral_avgDirac]
      simp
  obtain ⟨hYi, hEY⟩ := hsnd (fun x => φ ⬝ᵥ x) hdotc
  obtain ⟨hY2i, hEY2⟩ := hsnd (fun x => (φ ⬝ᵥ x) ^ 2) (hdotc.pow 2)
  have hEY' : ∫ w, Y w ∂π = m := by rw [hEY]; rfl
  have hEY2' : ∫ w, Y w ^ 2 ∂π = S := by rw [hEY2]; rfl
  -- Hölder bound
  have hZL : ∀ w, |Z w| ≤ N * L w := fun w => holder_dot p q hq hqtop hpq φ (w.1 - w.2)
  have hZ2i : Integrable (fun w => Z w ^ 2) π := by
    refine Integrable.mono' (hL2.const_mul (N ^ 2)) (hZc.pow 2).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_pow, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZL w) 2
  have hZi : Integrable Z π := by
    refine Integrable.mono' (((integrable_const (1:ℝ)).add hL2).const_mul N)
      hZc.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs]
    have hN : 0 ≤ N := norm_nonneg _
    have hL0 : 0 ≤ L w := norm_nonneg _
    have : L w ≤ 1 + L w ^ 2 := by nlinarith [sq_nonneg (L w - 1)]
    calc |Z w| ≤ N * L w := hZL w
      _ ≤ N * (1 + L w ^ 2) := mul_le_mul_of_nonneg_left this hN
  have hYZi : Integrable (fun w => Y w * Z w) π := by
    refine Integrable.mono' (hY2i.add hZ2i) (hYc.mul hZc).aestronglyMeasurable
      (ae_of_all _ fun w => ?_)
    show ‖Y w * Z w‖ ≤ Y w ^ 2 + Z w ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    simp only [hYdef]
    nlinarith [sq_nonneg (|φ ⬝ᵥ w.2| - |Z w|), sq_abs (φ ⬝ᵥ w.2), sq_abs (Z w),
      abs_nonneg (φ ⬝ᵥ w.2), abs_nonneg (Z w)]
  set c := ∫ w, Z w ∂π with hcdef
  set T := ∫ w, Z w ^ 2 ∂π with hTdef
  set J := ∫ w, Y w * Z w ∂π with hJdef
  -- pMean and pSecond in terms of the coupling
  have hfst : ∀ g : (Fin d → ℝ) → ℝ, Continuous g → ∫ x, g x ∂P = ∫ w, g w.1 ∂π := by
    intro g hg
    rw [← h1, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]
  have hsplit : ∀ w : (Fin d → ℝ) × (Fin d → ℝ), φ ⬝ᵥ w.1 = Y w + Z w := by
    intro w; simp only [hYdef, hZdef, dotProduct_sub]; ring
  have hmean : pMean P φ = m + c := by
    unfold pMean
    rw [hfst _ hdotc]
    simp only [hsplit]
    rw [integral_add hYi hZi, hEY']
  have hsecond : pSecond P φ = S + 2 * J + T := by
    unfold pSecond
    rw [hfst (fun x => (φ ⬝ᵥ x) ^ 2) (hdotc.pow 2)]
    simp only [hsplit]
    have := int_lin hYi hY2i hZi hZ2i hYZi 0 0 1 0 1 2
    rw [← hEY2']
    rw [show (fun w => (Y w + Z w) ^ 2) = fun w =>
      (0 + 0 * Y w + 1 * Y w ^ 2 + 0 * Z w + 1 * Z w ^ 2 + 2 * (Y w * Z w)) from
        funext fun w => by ring]
    rw [this]; ring
  have hVS : V = S - m ^ 2 := by
    have := (empVar_eq_aux R φ); simpa [hVdef, hSdef, hmdef] using this
  have hT : T ≤ N ^ 2 * t := by
    calc T ≤ ∫ w, N ^ 2 * L w ^ 2 ∂π := by
          refine integral_mono hZ2i (hL2.const_mul _) fun w => ?_
          have := pow_le_pow_left₀ (abs_nonneg _) (hZL w) 2
          rw [sq_abs, mul_pow] at this; exact this
      _ = N ^ 2 * ∫ w, L w ^ 2 ∂π := integral_const_mul _ _
      _ ≤ N ^ 2 * t := mul_le_mul_of_nonneg_left hEL2 (by positivity)
  have hc2 : c ^ 2 ≤ T := by
    have h0 : 0 ≤ ∫ w, (Z w - c) ^ 2 ∂π := integral_nonneg fun w => sq_nonneg _
    rw [show (fun w => (Z w - c) ^ 2) = fun w =>
      (c ^ 2 + 0 * Y w + 0 * Y w ^ 2 + (-2 * c) * Z w + 1 * Z w ^ 2 + 0 * (Y w * Z w)) from
        funext fun w => by ring] at h0
    rw [int_lin hYi hY2i hZi hZ2i hYZi] at h0
    rw [← hcdef, ← hTdef] at h0
    nlinarith
  have hCS : J - m * c ≤ Real.sqrt V * Real.sqrt (T - c ^ 2) := by
    have hq : ∀ s : ℝ, 0 ≤ V * (s * s) + (-2 * (J - m * c)) * s + (T - c ^ 2) := by
      intro s
      have h0 : 0 ≤ ∫ w, (s * (Y w - m) - (Z w - c)) ^ 2 ∂π := integral_nonneg fun w => sq_nonneg _
      rw [show (fun w => (s * (Y w - m) - (Z w - c)) ^ 2) = fun w =>
        ((s ^ 2 * m ^ 2 - 2 * s * m * c + c ^ 2) + (-2 * s ^ 2 * m + 2 * s * c) * Y w
          + s ^ 2 * Y w ^ 2 + (2 * s * m - 2 * c) * Z w + 1 * Z w ^ 2 + (-2 * s) * (Y w * Z w)) from
          funext fun w => by ring] at h0
      rw [int_lin hYi hY2i hZi hZ2i hYZi, hEY', hEY2', ← hcdef, ← hTdef, ← hJdef] at h0
      rw [hVS]; nlinarith [h0]
    have hdisc := discrim_le_zero hq
    unfold discrim at hdisc
    have hV0 : 0 ≤ V := empVar_nonneg_aux R φ
    have hK2 : (J - m * c) ^ 2 ≤ V * (T - c ^ 2) := by nlinarith
    calc J - m * c ≤ |J - m * c| := le_abs_self _
      _ = Real.sqrt ((J - m * c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (V * (T - c ^ 2)) := Real.sqrt_le_sqrt hK2
      _ = Real.sqrt V * Real.sqrt (T - c ^ 2) := Real.sqrt_mul hV0 _
  refine ⟨T, ?_, hT, ?_⟩
  · rw [hmean]; simpa using hc2
  · rw [hsecond, hmean]
    simp only [add_sub_cancel_left]
    nlinarith [hCS]

end DRMeanVar.Reform


open MeasureTheory

namespace DRMeanVar.Reform
open DRMVAux

theorem le_of_right_limit_aux {f : ℝ → ℝ} {x δ : ℝ} (hf : ContinuousAt f δ)
    (h : ∀ t, δ < t → x ≤ f t) : x ≤ f δ :=
  ge_of_tendsto (hf.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi δ)))
    (eventually_nhdsWithin_of_forall (s := Set.Ioi δ) fun t ht => h t ht)

theorem prop1_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ) :
    IsLeast ((fun P => pMean P φ) '' U q δ R)
      (empMean R φ - Real.sqrt δ * ‖WithLp.toLp p φ‖) := by
  haveI : Fact (1 ≤ p) := ⟨hpq.one_le⟩
  have hN : 0 ≤ ‖WithLp.toLp p φ‖ := norm_nonneg _
  constructor
  · obtain ⟨P, hP, hm, -⟩ := attain_aux R q p δ (empMean R φ - Real.sqrt δ * ‖WithLp.toLp p φ‖)
      hδ hq hqtop hpq φ (by
        rw [show empMean R φ - Real.sqrt δ * ‖WithLp.toLp p φ‖ - empMean R φ =
          -(Real.sqrt δ * ‖WithLp.toLp p φ‖) by ring, neg_sq, mul_pow, Real.sq_sqrt hδ]
        simp)
    exact ⟨P, hP, hm⟩
  · rintro _ ⟨P, hP, rfl⟩
    have key : empMean R φ - pMean P φ ≤ Real.sqrt δ * ‖WithLp.toLp p φ‖ := by
      refine le_of_right_limit_aux (f := fun t => Real.sqrt t * ‖WithLp.toLp p φ‖)
        ((Real.continuous_sqrt.mul continuous_const).continuousAt) fun t ht => ?_
      obtain ⟨T, hc2, hT, -⟩ := upper_aux R q p δ hδ hq hqtop hpq φ P hP t ht
      have ht0 : 0 ≤ t := hδ.trans ht.le
      have h1 : (pMean P φ - empMean R φ) ^ 2 ≤ (Real.sqrt t * ‖WithLp.toLp p φ‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ht0]; linarith
      have hB : 0 ≤ Real.sqrt t * ‖WithLp.toLp p φ‖ := by positivity
      show empMean R φ - pMean P φ ≤ Real.sqrt t * ‖WithLp.toLp p φ‖
      by_contra hcon
      push_neg at hcon
      nlinarith [h1, hB, hcon]
    linarith

theorem prop3_aux {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ α : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    IsGreatest {v : ℝ | ∃ P ∈ U q δ R, pMean P φ = α ∧ v = pSecond P φ}
      (hFun p δ R α φ) := by
  constructor
  · obtain ⟨P, hP, hm, hs⟩ := attain_aux R q p δ α hδ hq hqtop hpq φ hfeas
    exact ⟨P, hP, hm, hs.symm⟩
  · rintro _ ⟨P, hP, hm, rfl⟩
    set f : ℝ → ℝ := fun t => empSecond R φ + 2 * (α - empMean R φ) * empMean R φ +
      t * ‖WithLp.toLp p φ‖ ^ 2 +
      2 * Real.sqrt (t * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2) *
        Real.sqrt (empVar R φ) with hfdef
    have hfδ : f δ = hFun p δ R α φ := rfl
    rw [← hfδ]
    refine le_of_right_limit_aux (by rw [hfdef]; fun_prop) fun t ht => ?_
    obtain ⟨T, hc2, hT, hs⟩ := upper_aux R q p δ hδ hq hqtop hpq φ P hP t ht
    rw [hm] at hc2 hs
    have h1 : Real.sqrt (T - (α - empMean R φ) ^ 2) ≤
        Real.sqrt (t * ‖WithLp.toLp p φ‖ ^ 2 - (α - empMean R φ) ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 := Real.sqrt_nonneg (empVar R φ)
    simp only [hfdef]
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]

end DRMeanVar.Reform

open DRMeanVar.Reform in
theorem solution {d n : ℕ} [NeZero n] (R : Fin n → (Fin d → ℝ))
    (q p : ENNReal) (δ α : ℝ) (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) (φ : Fin d → ℝ)
    (hfeas : (α - empMean R φ) ^ 2 - δ * ‖WithLp.toLp p φ‖ ^ 2 ≤ 0) :
    IsGreatest {v : ℝ | ∃ P ∈ U q δ R, pMean P φ = α ∧ v = pSecond P φ}
      (hFun p δ R α φ) :=
  prop3_aux R q p δ α hδ hq hqtop hpq φ hfeas
