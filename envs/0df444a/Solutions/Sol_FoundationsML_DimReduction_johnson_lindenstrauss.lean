-- Prove2me | solution 1 for FoundationsML.DimReduction.johnson_lindenstrauss
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:33:35.211995+00:00
-- url     : https://prove2.me/submissions/13a9032e-d1f3-45f3-bfc6-90e2231811c1

import Mathlib
import Definitions.Def_FoundationsML_DimReduction_IsChiSquaredMGF
import Definitions.Def_FoundationsML_DimReduction_IsIIDStandardGaussianMatrix
import Definitions.Def_FoundationsML_DimReduction_SqNorm

open MeasureTheory ProbabilityTheory

namespace FoundationsML.DimReduction


lemma chi_log_upper {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hx : |(-ε)| < 1 := by rw [abs_neg, abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 6
  rw [abs_neg, abs_of_pos h0, sub_neg_eq_add] at h
  simp [Finset.sum_range_succ] at h
  have h' := (abs_le.mp h).2
  have e3 : (-ε) ^ 3 = -ε ^ 3 := by ring
  have e4 : (-ε) ^ 4 = ε ^ 4 := by ring
  have e5 : (-ε) ^ 5 = -ε ^ 5 := by ring
  have e6 : (-ε) ^ 6 = ε ^ 6 := by ring
  rw [e3, e4, e5, e6] at h'
  norm_num at h'
  have hd : ε ^ 7 / (1 - ε) ≤ 2 * ε ^ 7 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos (pow_pos h0 7) h0]
  have p : ε ^ 7 ≤ ε ^ 3 / 16 := by
    have : ε ^ 4 ≤ (1/2) ^ 4 := pow_le_pow_left₀ h0.le h1.le 4
    nlinarith [pow_pos h0 3]
  have q : ε ^ 5 ≤ ε ^ 3 / 4 := by
    have : ε ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0.le h1.le 2
    nlinarith [pow_pos h0 3]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 6]

lemma chi_log_lower {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Real.log (1 - ε) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 := by
  have hx : |ε| < 1 := by rw [abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 4
  rw [abs_of_pos h0] at h
  simp [Finset.sum_range_succ] at h
  have h' := (abs_le.mp h).2
  norm_num at h'
  have hd : ε ^ 5 / (1 - ε) ≤ 2 * ε ^ 5 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_pos (pow_pos h0 5) h0]
  nlinarith [pow_pos h0 3, pow_pos h0 4, pow_pos h0 5, mul_pos (pow_pos h0 3) h0,
    mul_pos (pow_pos h0 3) (pow_pos h0 2)]

lemma chi_integrable {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} {Q : Ω → ℝ} {k : ℕ}
    (hQ : IsChiSquaredMGF Prob Q k) {lam : ℝ} (hl : lam < 1 / 2) :
    Integrable (fun ω => Real.exp (lam * Q ω)) Prob := by
  by_contra hni
  have := hQ lam hl
  rw [integral_undef hni] at this
  have hpos : 0 < (1 - 2 * lam) ^ (-(k : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  linarith

theorem chi_main {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] (Q : Ω → ℝ) (k : ℕ) (hQ : IsChiSquaredMGF Prob Q k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set B := Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) with hB
  -- upper tail
  set t := ε / (2 * (1 + ε)) with ht
  have ht0 : 0 ≤ t := by positivity
  have htl : t < 1 / 2 := by rw [ht, div_lt_iff₀ (by positivity)]; linarith
  have hup := measure_ge_le_exp_mul_mgf (μ := Prob) (X := Q) ((1 + ε) * k) ht0
    (chi_integrable hQ htl)
  have hmgf1 : mgf Q Prob t = (1 - 2 * t) ^ (-(k : ℝ) / 2) := hQ t htl
  have h12t : 1 - 2 * t = (1 + ε)⁻¹ := by rw [ht]; field_simp <;> ring
  have hupB : Prob.real {ω | (1 + ε) * k ≤ Q ω} ≤ B := by
    refine hup.trans (le_of_eq_of_le (by rw [hmgf1]) ?_)
    rw [h12t, Real.rpow_def_of_pos (by positivity), Real.log_inv, ← Real.exp_add, hB,
      Real.exp_le_exp]
    have hl := chi_log_upper hε0 hε1
    have : -t * ((1 + ε) * k) = -(ε * k / 2) := by rw [ht]; field_simp <;> ring
    rw [this]
    nlinarith [mul_nonneg hk (by nlinarith : (0:ℝ) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 + ε))]
  -- lower tail
  set s := -(ε / (2 * (1 - ε))) with hs
  have h1e' : (0 : ℝ) < 1 - ε := by linarith
  have hs0 : s ≤ 0 := by rw [hs]; exact neg_nonpos.mpr (by positivity)
  have hsl : s < 1 / 2 := by linarith
  have hlo := measure_le_le_exp_mul_mgf (μ := Prob) (X := Q) ((1 - ε) * k) hs0
    (chi_integrable hQ hsl)
  have hmgf2 : mgf Q Prob s = (1 - 2 * s) ^ (-(k : ℝ) / 2) := hQ s hsl
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have h12s : 1 - 2 * s = (1 - ε)⁻¹ := by rw [hs]; field_simp <;> ring
  have hloB : Prob.real {ω | Q ω ≤ (1 - ε) * k} ≤ B := by
    refine hlo.trans (le_of_eq_of_le (by rw [hmgf2]) ?_)
    rw [h12s, Real.rpow_def_of_pos (by positivity), Real.log_inv, ← Real.exp_add, hB,
      Real.exp_le_exp]
    have hl := chi_log_lower hε0 hε1
    have : -s * ((1 - ε) * k) = ε * k / 2 := by rw [hs]; field_simp
    rw [this]
    nlinarith [mul_nonneg hk (by nlinarith : (0:ℝ) ≤ -ε - ε ^ 2 / 2 + ε ^ 3 / 2 - Real.log (1 - ε))]
  -- combine
  set E := {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)}
  have hsub : Eᶜ ⊆ {ω | (1 + ε) * k ≤ Q ω} ∪ {ω | Q ω ≤ (1 - ε) * k} := by
    intro ω hω
    simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
    rcases hω with h | h
    · right; exact h.le
    · left; exact h.le
  have h1 : (1 : ℝ) ≤ Prob.real E + Prob.real Eᶜ := by
    have := measureReal_union_le (μ := Prob) E Eᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  have h2 := (measureReal_mono (μ := Prob) hsub).trans (measureReal_union_le _ _)
  linarith


lemma gauss_sq_mgf {lam : ℝ} (hl : lam < 1 / 2) :
    ∫ x, Real.exp (lam * x ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * lam) ^ (-(1 : ℝ) / 2) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hb : 0 < 1 / 2 - lam := by linarith
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (lam * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - lam) * x ^ 2) := by
    intro x
    simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  simp_rw [e]
  rw [integral_const_mul, integral_gaussian]
  have e1 : Real.pi / (1 / 2 - lam) = (2 * Real.pi) / (1 - 2 * lam) := by
    field_simp <;> ring
  have h2 : 0 < 1 - 2 * lam := by linarith
  rw [e1, Real.sqrt_div (by positivity), show -(1 : ℝ) / 2 = -(1 / 2) by ring,
    Real.rpow_neg h2.le, ← Real.sqrt_eq_rpow]
  have : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma row_law {N : ℕ} (c : Fin N → ℝ) (hc : ∑ j, c j ^ 2 = 1) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (fun g => ∑ j, c j * g j) =
      gaussianReal 0 1 := by
  set ν := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  have hmj : ∀ j, Measurable (fun g : Fin N → ℝ => g j) := fun j => measurable_pi_apply j
  have hind : iIndepFun (fun j (g : Fin N → ℝ) => c j * g j) ν :=
    iIndepFun_pi (X := fun j (t : ℝ) => c j * t) (fun j => by fun_prop)
  have hev : ∀ j, ν.map (fun g : Fin N → ℝ => g j) = gaussianReal 0 1 := fun j =>
    (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) j).map_eq
  have hG0 : ∀ j, HasGaussianLaw (fun g : Fin N → ℝ => g j) ν := by
    intro j
    haveI : IsGaussian (ν.map (fun g : Fin N → ℝ => g j)) := by rw [hev j]; infer_instance
    exact IsGaussian.hasGaussianLaw
  have hG : ∀ j, HasGaussianLaw (fun g : Fin N → ℝ => c j * g j) ν := fun j =>
    by simpa [smul_eq_mul] using (hG0 j).fun_smul (c j)
  have hS := hind.hasGaussianLaw_fun_sum hG
  rw [hS.map_eq_gaussianReal]
  have hmean : ∫ g, ∑ j, c j * g j ∂ν = 0 := by
    rw [integral_finset_sum _ (fun j _ => ((hG j).integrable))]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul]
    have : ∫ g, g j ∂ν = 0 := by
      rw [show (∫ g, g j ∂ν) = ∫ t, t ∂(ν.map (fun g : Fin N → ℝ => g j)) from
        (integral_map (hmj j).aemeasurable aestronglyMeasurable_id).symm, hev j,
        integral_id_gaussianReal]
    rw [this, mul_zero]
  have hvar1 : ∀ j, Var[fun g : Fin N → ℝ => g j; ν] = 1 := by
    intro j
    have := variance_map (μ := ν) (X := id) (Y := fun g : Fin N → ℝ => g j)
      aemeasurable_id (hmj j).aemeasurable
    rw [hev j, variance_id_gaussianReal] at this
    simpa using this.symm
  have hvar : Var[fun g : Fin N → ℝ => ∑ j, c j * g j; ν] = 1 := by
    have h := IndepFun.variance_sum (μ := ν) (X := fun j (g : Fin N → ℝ) => c j * g j)
      (s := Finset.univ) (fun j _ => (hG j).memLp_two)
      (fun i _ j _ hij => hind.indepFun hij)
    have hfun : (∑ j ∈ Finset.univ, fun g : Fin N → ℝ => c j * g j) =
        fun g => ∑ j, c j * g j := by ext g; simp
    rw [hfun] at h
    rw [h, ← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (fun g : Fin N → ℝ => c j * g j) = fun g => c j * (fun g : Fin N → ℝ => g j) g
      from rfl, variance_const_mul, hvar1 j, mul_one]
  rw [hmean, hvar]
  simp

lemma row_mgf {N : ℕ} (c : Fin N → ℝ) (hc : ∑ j, c j ^ 2 = 1) {lam : ℝ} (hl : lam < 1 / 2) :
    ∫ g, Real.exp (lam * (∑ j, c j * g j) ^ 2) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1))
      = (1 - 2 * lam) ^ (-(1 : ℝ) / 2) := by
  have hSm : Measurable (fun g : Fin N → ℝ => ∑ j, c j * g j) :=
    Finset.measurable_sum _ fun j _ => (measurable_const.mul (measurable_pi_apply j))
  have h := integral_map (μ := Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (f := fun y : ℝ => Real.exp (lam * y ^ 2)) hSm.aemeasurable (by fun_prop)
  rw [row_law c hc] at h
  rw [← h, gauss_sq_mgf hl]

theorem gp_main {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] {N k : ℕ}
    (A : Ω → Matrix (Fin k) (Fin N) ℝ) (hA : IsIIDStandardGaussianMatrix Prob A)
    (x : Fin N → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * SqNorm x ≤
          SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ∧
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ≤ (1 + ε) * SqNorm x} := by
  set S := SqNorm x with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- degenerate case x = 0
  rcases hS0.eq_or_lt with hS | hSpos
  · have hx : x = 0 := by
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp hS.symm j
        (Finset.mem_univ _)
      simpa using this
    have hset : {ω | (1 - ε) * S ≤ SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ∧
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ≤ (1 + ε) * S} = Set.univ := by
      ext ω; simp [← hS, hx, SqNorm]
    rw [hset, probReal_univ]
    linarith [Real.exp_pos (-(ε ^ 2 - ε ^ 3) * k / 4)]
  -- degenerate case k = 0
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.exp_zero]
    linarith [measureReal_nonneg (μ := Prob) (s := {ω | (1 - ε) * S ≤
          SqNorm (fun j => (1 / Real.sqrt ((0 : ℕ) : ℝ)) * (A ω).mulVec x j) ∧
        SqNorm (fun j => (1 / Real.sqrt ((0 : ℕ) : ℝ)) * (A ω).mulVec x j) ≤ (1 + ε) * S})]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set nx := Real.sqrt S with hnx
  have hnxpos : 0 < nx := Real.sqrt_pos.mpr hSpos
  set c : Fin N → ℝ := fun j => x j / nx with hcdef
  have hc : ∑ j, c j ^ 2 = 1 := by
    simp only [hcdef, div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt hS0]
    exact div_self hSpos.ne'
  set Q : Ω → ℝ := fun ω => ∑ i, (∑ j, c j * A ω i j) ^ 2 with hQdef
  -- law of the entries
  have hmeas : ∀ p : Fin k × Fin N, AEMeasurable (fun ω => A ω p.1 p.2) Prob := by
    intro p
    by_contra h
    have := hA.isGaussian p.1 p.2
    rw [Measure.map_of_not_aemeasurable h] at this
    have h1 := congrArg (fun μ : Measure ℝ => μ Set.univ) this
    simp at h1
  set W : Ω → (Fin k × Fin N → ℝ) := fun ω p => A ω p.1 p.2 with hW
  have hWm : AEMeasurable W Prob := aemeasurable_pi_lambda _ hmeas
  have hlaw : Prob.map W = Measure.infinitePi (fun _ : Fin k × Fin N => gaussianReal 0 1) := by
    rw [hA.indep.map_fun_eq_infinitePi_map₀ hWm]
    congr 1
    funext p
    exact hA.isGaussian p.1 p.2
  have hrows : (Measure.infinitePi (fun _ : Fin k × Fin N => gaussianReal 0 1)).map
      (MeasurableEquiv.curry (Fin k) (Fin N) ℝ) =
      Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
    rw [Measure.infinitePi_map_curry (fun (_ : Fin k) (_ : Fin N) => gaussianReal (0 : ℝ) 1)]
    simp only [Measure.infinitePi_eq_pi]
  have hchi : IsChiSquaredMGF Prob Q k := by
    intro lam hl
    have h1 : ∫ ω, Real.exp (lam * Q ω) ∂Prob =
        ∫ a, Real.exp (lam * ∑ i, (∑ j, c j * a (i, j)) ^ 2) ∂(Prob.map W) := by
      have hcont : Continuous (fun a : Fin k × Fin N → ℝ =>
          Real.exp (lam * ∑ i, (∑ j, c j * a (i, j)) ^ 2)) := by fun_prop
      rw [integral_map hWm hcont.aestronglyMeasurable]
    rw [h1, hlaw]
    have h2 : ∫ a, Real.exp (lam * ∑ i, (∑ j, c j * a (i, j)) ^ 2)
          ∂(Measure.infinitePi (fun _ : Fin k × Fin N => gaussianReal 0 1)) =
        ∫ r, Real.exp (lam * ∑ i, (∑ j, c j * r i j) ^ 2)
          ∂((Measure.infinitePi (fun _ : Fin k × Fin N => gaussianReal 0 1)).map
            (MeasurableEquiv.curry (Fin k) (Fin N) ℝ)) := by
      rw [integral_map_equiv]; rfl
    rw [h2, hrows]
    have h3 : ∀ r : Fin k → Fin N → ℝ, Real.exp (lam * ∑ i, (∑ j, c j * r i j) ^ 2) =
        ∏ i, Real.exp (lam * (∑ j, c j * r i j) ^ 2) := by
      intro r; rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [h3]
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin k) (g : Fin N → ℝ) =>
      Real.exp (lam * (∑ j, c j * g j) ^ 2))]
    simp_rw [row_mgf c hc hl]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
      ← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have hmain := chi_main Prob Q k hchi ε hε0 hε1
  -- identify the events
  have hval : ∀ ω, SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) = S / k * Q ω := by
    intro ω
    simp only [SqNorm, hQdef, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsk : (1 / Real.sqrt k) ^ 2 = 1 / k := by
      rw [div_pow, Real.sq_sqrt hkR.le, one_pow]
    have hxj : ∀ j, x j = nx * c j := by
      intro j; simp only [hcdef]; field_simp
    have : ∑ j, A ω i j * x j = nx * ∑ j, c j * A ω i j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; rw [hxj j]; ring
    rw [mul_pow, hsk, this, mul_pow, hnx, Real.sq_sqrt hS0]
    ring
  have hset : {ω | (1 - ε) * S ≤ SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ∧
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ≤ (1 + ε) * S} =
      {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, hval ω]
    have hSk : 0 < S / k := div_pos hSpos hkR
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have : S / k * ((1 - ε) * k) ≤ S / k * Q ω := by
          rw [show S / k * ((1 - ε) * k) = (1 - ε) * S by field_simp]; exact h1
        exact le_of_mul_le_mul_left this hSk
      · have : S / k * Q ω ≤ S / k * ((1 + ε) * k) := by
          rw [show S / k * ((1 + ε) * k) = (1 + ε) * S by field_simp]; exact h2
        exact le_of_mul_le_mul_left this hSk
    · rintro ⟨h1, h2⟩
      constructor
      · rw [show (1 - ε) * S = S / k * ((1 - ε) * k) by field_simp]
        exact mul_le_mul_of_nonneg_left h1 hSk.le
      · rw [show (1 + ε) * S = S / k * ((1 + ε) * k) by field_simp]
        exact mul_le_mul_of_nonneg_left h2 hSk.le
  rw [hset]
  exact hmain


theorem jl_main {N : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (m : ℕ) (hm : 4 < m) (V : Finset (Fin N → ℝ)) (hV : V.card = m) :
    ∃ f : (Fin N → ℝ) → (Fin ⌈20 * Real.log (m : ℝ) / ε ^ 2⌉₊ → ℝ),
      ∀ u ∈ V, ∀ v ∈ V,
        (1 - ε) * SqNorm (u - v) ≤ SqNorm (f u - f v) ∧
          SqNorm (f u - f v) ≤ (1 + ε) * SqNorm (u - v) := by
  set k := ⌈20 * Real.log (m : ℝ) / ε ^ 2⌉₊ with hkdef
  set μ : Measure (Fin k × Fin N → ℝ) := Measure.pi (fun _ => gaussianReal 0 1) with hμ
  let A : (Fin k × Fin N → ℝ) → Matrix (Fin k) (Fin N) ℝ := fun ω => Matrix.of fun i j => ω (i, j)
  have hA : IsIIDStandardGaussianMatrix μ A := by
    refine ⟨fun i j => ?_, ?_⟩
    · exact (measurePreserving_eval (fun _ : Fin k × Fin N => gaussianReal 0 1) (i, j)).map_eq
    · exact iIndepFun_pi (X := fun _ (t : ℝ) => t) (fun _ => aemeasurable_id)
  -- the good event for a pair
  set E : (Fin N → ℝ) × (Fin N → ℝ) → Set (Fin k × Fin N → ℝ) := fun p =>
    {ω | (1 - ε) * SqNorm (p.1 - p.2) ≤
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec (p.1 - p.2) j) ∧
      SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec (p.1 - p.2) j) ≤
        (1 + ε) * SqNorm (p.1 - p.2)} with hE
  have hEm : ∀ p, MeasurableSet (E p) := by
    intro p
    have hc : Continuous fun ω : Fin k × Fin N → ℝ =>
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec (p.1 - p.2) j) := by
      simp only [SqNorm, Matrix.mulVec, dotProduct, A, Matrix.of_apply]
      fun_prop
    exact (measurableSet_le measurable_const hc.measurable).inter
      (measurableSet_le hc.measurable measurable_const)
  set a := (ε ^ 2 - ε ^ 3) * (k : ℝ) / 4 with ha
  have hpair : ∀ p, μ.real (E p)ᶜ ≤ 2 * Real.exp (-a) := by
    intro p
    have h := gp_main μ A hA (p.1 - p.2) ε hε0 hε1
    rw [measureReal_compl (hEm p), probReal_univ]
    have : -(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4 = -a := by rw [ha]; ring
    rw [this] at h
    linarith
  -- numerics
  have hm5 : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : Real.log 4 < Real.log m := Real.log_lt_log (by norm_num) (by linarith)
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hk : 20 * Real.log m / ε ^ 2 ≤ k := Nat.le_ceil _
  have hε2 : 0 < ε ^ 2 := by positivity
  have hapos : 5 / 2 * Real.log m ≤ a := by
    have h1 : ε ^ 2 / 2 ≤ ε ^ 2 - ε ^ 3 := by nlinarith
    have h2 : 20 * Real.log m ≤ ε ^ 2 * k := by
      rw [div_le_iff₀ hε2] at hk; linarith
    rw [ha]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 hk0]
  have hbound : (m : ℝ) ^ 2 * (2 * Real.exp (-a)) < 1 := by
    have e1 : (m : ℝ) ^ 2 = Real.exp (2 * Real.log m) := by
      have hmpos : (0 : ℝ) < m := by linarith
      rw [show 2 * Real.log m = Real.log m + Real.log m by ring, Real.exp_add, Real.exp_log hmpos]
      ring
    have h1 : Real.exp (-a) ≤ Real.exp (-(5 / 2 * Real.log m)) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 * Real.exp (-(1 / 2 * Real.log m)) < 1 := by
      have : Real.log 2 < 1 / 2 * Real.log m := by
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      have h3 : 2 < Real.exp (1 / 2 * Real.log m) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ < Real.exp (1 / 2 * Real.log m) := Real.exp_lt_exp.mpr this
      rw [Real.exp_neg]
      have := Real.exp_pos (1 / 2 * Real.log m)
      rw [← div_eq_mul_inv, div_lt_one this]; exact h3
    calc (m : ℝ) ^ 2 * (2 * Real.exp (-a)) ≤ Real.exp (2 * Real.log m) *
          (2 * Real.exp (-(5 / 2 * Real.log m))) := by
            rw [e1]; gcongr
      _ = 2 * Real.exp (-(1 / 2 * Real.log m)) := by
            rw [mul_left_comm, ← Real.exp_add]; ring_nf
      _ < 1 := h2
  -- a good ω exists
  have hne : (⋂ p ∈ V ×ˢ V, E p).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hcov : (Set.univ : Set (Fin k × Fin N → ℝ)) ⊆ ⋃ p ∈ V ×ˢ V, (E p)ᶜ := by
      intro ω _
      by_contra hω
      simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hω
      have : ω ∈ ⋂ p ∈ V ×ˢ V, E p := by
        simp only [Set.mem_iInter]; exact fun p hp => hω p hp
      rw [hemp] at this; exact this
    have h1 := (measureReal_mono (μ := μ) hcov (measure_ne_top _ _)).trans
      (measureReal_biUnion_finset_le (V ×ˢ V) (fun p => (E p)ᶜ))
    rw [probReal_univ] at h1
    have h2 : ∑ p ∈ V ×ˢ V, μ.real (E p)ᶜ ≤ ((V ×ˢ V).card : ℝ) * (2 * Real.exp (-a)) := by
      rw [← nsmul_eq_mul]; exact Finset.sum_le_card_nsmul _ _ _ fun p _ => hpair p
    rw [Finset.card_product, hV] at h2
    push_cast at h2
    nlinarith
  obtain ⟨ω, hω⟩ := hne
  refine ⟨fun y j => (1 / Real.sqrt k) * (A ω).mulVec y j, fun u hu v hv => ?_⟩
  have h := (Set.mem_iInter₂.mp hω) (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩)
  have hfun : ((fun j => (1 / Real.sqrt k) * (A ω).mulVec u j) -
      fun j => (1 / Real.sqrt k) * (A ω).mulVec v j) =
      fun j => (1 / Real.sqrt k) * (A ω).mulVec (u - v) j := by
    funext j; simp [Matrix.mulVec_sub, mul_sub]
  rw [hfun]
  exact h

end FoundationsML.DimReduction

open FoundationsML.DimReduction

theorem solution {N : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (m : ℕ) (hm : 4 < m) (V : Finset (Fin N → ℝ)) (hV : V.card = m) :
    ∃ f : (Fin N → ℝ) → (Fin ⌈20 * Real.log (m : ℝ) / ε ^ 2⌉₊ → ℝ),
      ∀ u ∈ V, ∀ v ∈ V,
        (1 - ε) * SqNorm (u - v) ≤ SqNorm (f u - f v) ∧
          SqNorm (f u - f v) ≤ (1 + ε) * SqNorm (u - v) := by
  exact jl_main ε hε0 hε1 m hm V hV
