-- Prove2me | solution 2 for DemandSubstitution.Correlation.proposition2_profit_decreasing_in_correlation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:55:06.120809+00:00
-- url     : https://prove2.me/submissions/90e6055b-9c80-4a70-b6be-4e3a87fb73c2

import Mathlib
import Definitions.Def_DemandSubstitution_Correlation_Setting
import Theorems.Thm_HighDimProb_RandomProcesses_slepian_functional_linear

open MeasureTheory ProbabilityTheory Matrix WithLp DemandSubstitution.Correlation Filter Topology
open scoped MatrixOrder

/-! ### Part 1: Smooth bounded Müller–Scarsini comparison via Slepian's functional lemma -/

private noncomputable def linFromMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (Matrix.mulVecLin A).toContinuousLinearMap

private noncomputable def leftLift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin (2 * n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (linFromMat A).comp (ContinuousLinearMap.pi fun j : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * n + 1) => ℝ)
      ⟨j.1, by omega⟩)

private noncomputable def rightLift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin (2 * n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (linFromMat A).comp (ContinuousLinearMap.pi fun j : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * n + 1) => ℝ)
      ⟨n + j.1, by omega⟩)

private lemma normalLaw_eq_map_stdPi {n : ℕ} (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    normalLaw m S =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map
        (fun x => m + (CFC.sqrt S).mulVec x) := by
  have h1 : normalLaw m S =
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (fun x => WithLp.toLp 2 m + (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x)).map
        WithLp.ofLp := rfl
  rw [h1, ← ProbabilityTheory.map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

private lemma measurePreserving_pi_precomp_gauss {m n : ℕ} (ι : Fin m → Fin n)
    (hι : Function.Injective ι) :
    MeasurePreserving
      (fun x : Fin n → ℝ => fun j : Fin m => x (ι j))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
  refine ⟨by fun_prop, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  let t : Fin n → Set ℝ := fun k =>
    if h : ∃ j : Fin m, ι j = k then s (Classical.choose h) else Set.univ
  have hpre : (fun x : Fin n → ℝ => fun j : Fin m => x (ι j)) ⁻¹' Set.univ.pi s =
      Set.univ.pi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, t]
    constructor
    · intro hx k
      by_cases h : ∃ j : Fin m, ι j = k
      · rw [dif_pos h]
        have hspec : ι (Classical.choose h) = k := Classical.choose_spec h
        simpa [hspec] using hx (Classical.choose h)
      · rw [dif_neg h]
        trivial
    · intro hx j
      have h : ∃ j' : Fin m, ι j' = ι j := ⟨j, rfl⟩
      have hxj := hx (ι j)
      rw [dif_pos h] at hxj
      have hEq : Classical.choose h = j := hι (Classical.choose_spec h)
      rwa [hEq] at hxj
  rw [hpre, Measure.pi_pi]
  have hprod : ∏ k : Fin n, gaussianReal 0 1 (t k) =
      ∏ k ∈ Finset.univ.image ι, gaussianReal 0 1 (t k) := by
    symm
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have hnot : ¬ ∃ j : Fin m, ι j = k := by
      rintro ⟨j, rfl⟩
      exact hk (Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩)
    simp [t, dif_neg hnot]
  rw [hprod, Finset.prod_image (fun a _ b _ hab => hι hab)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ∃ j' : Fin m, ι j' = ι j := ⟨j, rfl⟩
  have hEq : Classical.choose h = j := hι (Classical.choose_spec h)
  simp [t, dif_pos h, hEq]

private lemma sqrt_gram_eq {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (i j : Fin n) :
    ∑ k : Fin n, (CFC.sqrt S) i k * (CFC.sqrt S) j k = S i j := by
  have hmul : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hsym : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint
  have htrans : ∀ a b, (CFC.sqrt S) b a = (CFC.sqrt S) a b := fun a b => by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hsym a) b
  have hij := congrFun (congrFun hmul i) j
  rw [Matrix.mul_apply] at hij
  calc
    ∑ k : Fin n, (CFC.sqrt S) i k * (CFC.sqrt S) j k
      = ∑ k : Fin n, (CFC.sqrt S) i k * (CFC.sqrt S) k j := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [htrans j k]
    _ = S i j := hij

private lemma muller_scarsini_normal_smooth_bounded {n : ℕ} (m : Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ)
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hdiag : ∀ k, S₁ k k = S₂ k k) (hle : ∀ k l, S₁ k l ≤ S₂ k l)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin n), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    ∫ x, f x ∂(normalLaw m S₁) ≤ ∫ x, f x ∂(normalLaw m S₂) := by
  let g : (Fin n → ℝ) → ℝ := fun y => f (m + y)
  have hg_cd : ContDiff ℝ 2 g := hf.comp (contDiff_const.add contDiff_id)
  have hg_fderiv : ∀ y, fderiv ℝ g y = fderiv ℝ f (m + y) := fun y =>
    fderiv_comp_add_left m
  have hg_ddf : ∀ y, fderiv ℝ (fderiv ℝ g) y = fderiv ℝ (fderiv ℝ f) (m + y) := fun y => by
    have hfun : fderiv ℝ g = fun z => fderiv ℝ f (m + z) := funext hg_fderiv
    rw [hfun]
    exact fderiv_comp_add_left m
  let M := leftLift (CFC.sqrt S₁)
  let L := rightLift (CFC.sqrt S₂)
  have hM_single : ∀ (k : Fin (2 * n + 1)),
      M (Pi.single k 1) =
        if hk : k.1 < n then fun i => (CFC.sqrt S₁) i ⟨k.1, hk⟩ else 0 := by
    intro k
    ext i
    simp only [M, leftLift, linFromMat, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    by_cases hk : k.1 < n
    · rw [dif_pos hk]
      rw [Finset.sum_eq_single ⟨k.1, hk⟩]
      · simp
      · intro b _ hb
        have hne : (⟨b.1, by omega⟩ : Fin (2 * n + 1)) ≠ k := by
          intro h
          have hv : b.1 = k.1 := congrArg Fin.val h
          exact hb (Fin.ext hv)
        simp [Pi.single_eq_of_ne hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hk]
      simp only [Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : (⟨j.1, by omega⟩ : Fin (2 * n + 1)) ≠ k := by
        intro h
        have hv : j.1 = k.1 := congrArg Fin.val h
        omega
      simp [Pi.single_eq_of_ne hne]
  have hL_single : ∀ (k : Fin (2 * n + 1)),
      L (Pi.single k 1) =
        if hk : n ≤ k.1 ∧ k.1 < 2 * n then fun i => (CFC.sqrt S₂) i ⟨k.1 - n, by omega⟩ else 0 := by
    intro k
    ext i
    simp only [L, rightLift, linFromMat, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
    by_cases hk : n ≤ k.1 ∧ k.1 < 2 * n
    · rw [dif_pos hk]
      rw [Finset.sum_eq_single ⟨k.1 - n, by omega⟩]
      · have heq : (⟨n + (k.1 - n), by omega⟩ : Fin (2 * n + 1)) = k :=
          Fin.ext (by change n + (k.1 - n) = k.1; omega)
        simp [heq]
      · intro b _ hb
        have hne : (⟨n + b.1, by omega⟩ : Fin (2 * n + 1)) ≠ k := by
          intro h
          have hv : n + b.1 = k.1 := congrArg Fin.val h
          exact hb (Fin.ext (by change b.1 = k.1 - n; omega))
        simp [Pi.single_eq_of_ne hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hk]
      simp only [Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : (⟨n + j.1, by omega⟩ : Fin (2 * n + 1)) ≠ k := by
        intro h
        have hv : n + j.1 = k.1 := congrArg Fin.val h
        omega
      simp [Pi.single_eq_of_ne hne]
  have hindep : ∀ k : Fin (2 * n + 1), L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0 := by
    intro k
    rw [hL_single k, hM_single k]
    by_cases hk : k.1 < n
    · left; rw [dif_neg (by omega)]
    · right; rw [dif_neg hk]
  have hM_cov : ∀ i j : Fin n,
      ∑ k : Fin (2 * n + 1), M (Pi.single k 1) i * M (Pi.single k 1) j = S₁ i j := by
    intro i j
    rw [← sqrt_gram_eq hS₁ i j]
    have hsub : ∑ k : Fin (2 * n + 1), M (Pi.single k 1) i * M (Pi.single k 1) j =
        ∑ k ∈ Finset.univ.image (fun a : Fin n => (⟨a.1, by omega⟩ : Fin (2 * n + 1))),
          M (Pi.single k 1) i * M (Pi.single k 1) j := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      have hnot : ¬ k.1 < n := by
        intro hlt
        apply hk
        exact Finset.mem_image.2 ⟨⟨k.1, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      rw [hM_single k, dif_neg hnot]
      simp
    rw [hsub, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [hM_single ⟨a.1, by omega⟩, dif_pos a.2]
    · intro a _ b _ h
      exact Fin.ext (by simpa using congrArg Fin.val h)
  have hL_cov : ∀ i j : Fin n,
      ∑ k : Fin (2 * n + 1), L (Pi.single k 1) i * L (Pi.single k 1) j = S₂ i j := by
    intro i j
    rw [← sqrt_gram_eq hS₂ i j]
    have hsub : ∑ k : Fin (2 * n + 1), L (Pi.single k 1) i * L (Pi.single k 1) j =
        ∑ k ∈ Finset.univ.image (fun a : Fin n => (⟨n + a.1, by omega⟩ : Fin (2 * n + 1))),
          L (Pi.single k 1) i * L (Pi.single k 1) j := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      have hnot : ¬ (n ≤ k.1 ∧ k.1 < 2 * n) := by
        intro ⟨h1, h2⟩
        apply hk
        exact Finset.mem_image.2 ⟨⟨k.1 - n, by omega⟩, Finset.mem_univ _,
          Fin.ext (by change n + (k.1 - n) = k.1; omega)⟩
      rw [hL_single k, dif_neg hnot]
      simp
    rw [hsub, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a _ => ?_
      have ha : n ≤ (⟨n + a.1, by omega⟩ : Fin (2 * n + 1)).1 ∧
          (⟨n + a.1, by omega⟩ : Fin (2 * n + 1)).1 < 2 * n := ⟨by dsimp; omega, by dsimp; omega⟩
      rw [hL_single ⟨n + a.1, by omega⟩, dif_pos ha]
      have hidx : (⟨n + a.1 - n, by omega⟩ : Fin n) = a := Fin.ext (by dsimp; omega)
      rw [hidx]
    · intro a _ b _ h
      have hv : n + a.1 = n + b.1 := congrArg Fin.val h
      exact Fin.ext (by omega)
  have hslep := HighDimProb.RandomProcesses.slepian_functional_linear L M hindep
    (fun i => by
      simp_rw [sq, hL_cov i i, hM_cov i i, hdiag i])
    (fun i j => by
      rw [hM_cov i j, hL_cov i j]
      exact hle i j)
    g hg_cd
    (fun y => hf_bound (m + y))
    (fun y => by rw [hg_fderiv]; exact hdf_bound (m + y))
    (fun y => by rw [hg_ddf]; exact hddf_bound (m + y))
    (fun y i j hij => by rw [hg_ddf]; exact hpositive (m + y) i j hij)
  have hmpL : MeasurePreserving
      (fun x : Fin (2 * n + 1) → ℝ => fun j : Fin n => x ⟨j.1, by omega⟩)
      (Measure.pi (fun _ : Fin (2 * n + 1) => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    measurePreserving_pi_precomp_gauss (fun j : Fin n => ⟨j.1, by omega⟩)
      (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  have hmpR : MeasurePreserving
      (fun x : Fin (2 * n + 1) → ℝ => fun j : Fin n => x ⟨n + j.1, by omega⟩)
      (Measure.pi (fun _ : Fin (2 * n + 1) => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    measurePreserving_pi_precomp_gauss (fun j : Fin n => ⟨n + j.1, by omega⟩)
      (fun a b h => Fin.ext (by have hv : n + a.1 = n + b.1 := congrArg Fin.val h; omega))
  have hint_M : ∫ x, f x ∂(normalLaw m S₁) =
      ∫ x, g (M x) ∂Measure.pi (fun _ : Fin (2 * n + 1) => gaussianReal 0 1) := by
    have hcont : Continuous (fun z : Fin n → ℝ => f (m + (CFC.sqrt S₁).mulVec z)) :=
      hf.continuous.comp (continuous_const.add (linFromMat (CFC.sqrt S₁)).continuous)
    rw [normalLaw_eq_map_stdPi,
      integral_map (by fun_prop) (hf.continuous.aestronglyMeasurable),
      ← hmpL.map_eq, integral_map hmpL.measurable.aemeasurable hcont.aestronglyMeasurable]
    rfl
  have hint_L : ∫ x, f x ∂(normalLaw m S₂) =
      ∫ x, g (L x) ∂Measure.pi (fun _ : Fin (2 * n + 1) => gaussianReal 0 1) := by
    have hcont : Continuous (fun z : Fin n → ℝ => f (m + (CFC.sqrt S₂).mulVec z)) :=
      hf.continuous.comp (continuous_const.add (linFromMat (CFC.sqrt S₂)).continuous)
    rw [normalLaw_eq_map_stdPi,
      integral_map (by fun_prop) (hf.continuous.aestronglyMeasurable),
      ← hmpR.map_eq, integral_map hmpR.measurable.aemeasurable hcont.aestronglyMeasurable]
    rfl
  rw [hint_M, hint_L]
  exact hslep

/-! ### Part 2: Smooth positive part `softplus` and smooth clamping `clamp` -/

private noncomputable def softplus (ε u : ℝ) : ℝ :=
  ε * Real.log (1 + Real.exp (u / ε))

private noncomputable def softplus' (ε u : ℝ) : ℝ :=
  Real.exp (u / ε) / (1 + Real.exp (u / ε))

private noncomputable def softplus'' (ε u : ℝ) : ℝ :=
  (1 / ε) * Real.exp (u / ε) / (1 + Real.exp (u / ε)) ^ 2

private lemma softplus_contDiff {ε : ℝ} : ContDiff ℝ 2 (softplus ε) := by
  unfold softplus
  refine contDiff_const.mul ?_
  exact (contDiff_const.add (Real.contDiff_exp.comp (contDiff_id.div_const ε))).log fun x =>
    (add_pos zero_lt_one (Real.exp_pos (x / ε))).ne'

private lemma hasDerivAt_softplus {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (softplus ε) (softplus' ε u) u := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t / ε)) (Real.exp (u / ε) * (1 / ε)) u := by
    simpa using ((hasDerivAt_id u).div_const ε).exp
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (t / ε)) (Real.exp (u / ε) * (1 / ε)) u :=
    h1.const_add 1
  have h3 : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (t / ε)))
      (Real.exp (u / ε) * (1 / ε) / (1 + Real.exp (u / ε))) u :=
    h2.log (by positivity)
  have h4 := h3.const_mul ε
  have heq : ε * (Real.exp (u / ε) * (1 / ε) / (1 + Real.exp (u / ε))) = softplus' ε u := by
    unfold softplus'
    field_simp [hε.ne']
  rw [heq] at h4
  exact h4

private lemma hasDerivAt_softplus' {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    HasDerivAt (softplus' ε) (softplus'' ε u) u := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t / ε)) (Real.exp (u / ε) * (1 / ε)) u := by
    simpa using ((hasDerivAt_id u).div_const ε).exp
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (t / ε)) (Real.exp (u / ε) * (1 / ε)) u :=
    h1.const_add 1
  have h3 := h1.div h2 (by positivity)
  have heq : (Real.exp (u / ε) * (1 / ε) * (1 + Real.exp (u / ε)) -
      Real.exp (u / ε) * (Real.exp (u / ε) * (1 / ε))) / (1 + Real.exp (u / ε)) ^ 2 =
      softplus'' ε u := by
    unfold softplus''
    field_simp [hε.ne']
    ring
  rw [heq] at h3
  exact h3

private lemma softplus'_nonneg (ε u : ℝ) : 0 ≤ softplus' ε u := by
  unfold softplus'; positivity

private lemma softplus'_le_one (ε u : ℝ) : softplus' ε u ≤ 1 := by
  unfold softplus'
  exact (div_le_one (by positivity)).2 (by linarith [Real.exp_pos (u / ε)])

private lemma abs_softplus'_le_one (ε u : ℝ) : |softplus' ε u| ≤ 1 := by
  rw [abs_of_nonneg (softplus'_nonneg ε u)]
  exact softplus'_le_one ε u

private lemma softplus''_nonneg {ε : ℝ} (hε : 0 < ε) (u : ℝ) : 0 ≤ softplus'' ε u := by
  unfold softplus''; positivity

private lemma abs_softplus''_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) : |softplus'' ε u| ≤ 1 / ε := by
  rw [abs_of_nonneg (softplus''_nonneg hε u)]
  unfold softplus''
  have he : 0 < Real.exp (u / ε) := Real.exp_pos (u / ε)
  have hden : 0 < (1 + Real.exp (u / ε)) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hle : Real.exp (u / ε) ≤ (1 + Real.exp (u / ε)) ^ 2 := by nlinarith
  have hpos : 0 ≤ 1 / ε := by positivity
  nlinarith

private lemma max_le_softplus {ε : ℝ} (hε : 0 < ε) (u : ℝ) : max u 0 ≤ softplus ε u := by
  unfold softplus
  refine max_le ?_ ?_
  · have h1 : Real.log (Real.exp (u / ε)) ≤ Real.log (1 + Real.exp (u / ε)) :=
      Real.log_le_log (Real.exp_pos _) (by linarith)
    rw [Real.log_exp] at h1
    have h2 : ε * (u / ε) ≤ ε * Real.log (1 + Real.exp (u / ε)) :=
      mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_div_cancel₀ u hε.ne'] at h2
  · exact mul_nonneg hε.le (Real.log_nonneg (by linarith [Real.exp_pos (u / ε)]))

private lemma softplus_nonneg {ε : ℝ} (hε : 0 < ε) (u : ℝ) : 0 ≤ softplus ε u :=
  (le_max_right u 0).trans (max_le_softplus hε u)

private lemma softplus_le_max_add {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    softplus ε u ≤ max u 0 + ε * Real.log 2 := by
  unfold softplus
  rcases le_total 0 u with hu | hu
  · have h1 : 1 ≤ Real.exp (u / ε) := Real.one_le_exp (div_nonneg hu hε.le)
    have h2 : Real.log (1 + Real.exp (u / ε)) ≤ Real.log (2 * Real.exp (u / ε)) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
    have h3 : ε * Real.log (1 + Real.exp (u / ε)) ≤ ε * (Real.log 2 + u / ε) :=
      mul_le_mul_of_nonneg_left h2 hε.le
    have h4 : ε * (Real.log 2 + u / ε) = u + ε * Real.log 2 := by
      field_simp [hε.ne']; ring
    linarith [le_max_left u 0]
  · have h1 : Real.exp (u / ε) ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg hu hε.le)
    have h2 : Real.log (1 + Real.exp (u / ε)) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : ε * Real.log (1 + Real.exp (u / ε)) ≤ ε * Real.log 2 :=
      mul_le_mul_of_nonneg_left h2 hε.le
    linarith [le_max_right u 0]

private lemma abs_softplus_sub_max_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    |softplus ε u - max u 0| ≤ ε * Real.log 2 := by
  rw [abs_of_nonneg (sub_nonneg.2 (max_le_softplus hε u))]
  linarith [softplus_le_max_add hε u]

private lemma abs_softplus_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    |softplus ε u| ≤ |u| + ε * Real.log 2 := by
  rw [abs_of_nonneg (softplus_nonneg hε u)]
  have hm : max u 0 ≤ |u| := max_le (le_abs_self u) (abs_nonneg u)
  linarith [softplus_le_max_add hε u]

private lemma tendsto_softplus {u : ℕ → ℝ} {L : ℝ} (hu : Tendsto u atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => softplus (1 / ((N : ℝ) + 1)) (u N)) atTop (𝓝 (max L 0)) := by
  have hmax : Tendsto (fun N : ℕ => max (u N) 0) atTop (𝓝 (max L 0)) :=
    hu.max tendsto_const_nhds
  have hzero : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * Real.log 2) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (Real.log 2)
  have hdiff : Tendsto (fun N : ℕ => softplus (1 / ((N : ℝ) + 1)) (u N) - max (u N) 0)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hzero
    have hε : 0 < 1 / ((N : ℝ) + 1) := by positivity
    simpa [Real.norm_eq_abs] using abs_softplus_sub_max_le hε (u N)
  simpa using hdiff.add hmax

private noncomputable def clamp (R t : ℝ) : ℝ :=
  R * Real.arctan (t / R)

private noncomputable def clamp' (R t : ℝ) : ℝ :=
  1 / (1 + (t / R) ^ 2)

private noncomputable def clamp'' (R t : ℝ) : ℝ :=
  -(2 * t / R ^ 2) / (1 + (t / R) ^ 2) ^ 2

private lemma clamp_contDiff (R : ℝ) : ContDiff ℝ 2 (clamp R) := by
  unfold clamp
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const R))

private lemma hasDerivAt_clamp {R : ℝ} (hR : 0 < R) (t : ℝ) :
    HasDerivAt (clamp R) (clamp' R t) t := by
  have h1 := ((Real.hasDerivAt_arctan (t / R)).comp t ((hasDerivAt_id t).div_const R)).const_mul R
  have heq : R * (1 / (1 + (t / R) ^ 2) * (1 / R)) = clamp' R t := by
    unfold clamp'
    field_simp [hR.ne']
  rw [heq] at h1
  exact h1

private lemma hasDerivAt_clamp' (R t : ℝ) :
    HasDerivAt (clamp' R) (clamp'' R t) t := by
  have h0 : HasDerivAt (fun s : ℝ => s / R) (1 / R) t := (hasDerivAt_id t).div_const R
  have hsq : HasDerivAt (fun s : ℝ => (s / R) ^ 2) ((2 : ℕ) * (t / R) ^ (2 - 1) * (1 / R)) t :=
    h0.pow 2
  have h1 : HasDerivAt (fun s : ℝ => 1 + (s / R) ^ 2) (2 * t / R ^ 2) t := by
    have hadd := hsq.const_add (1 : ℝ)
    have heq : ((2 : ℕ) : ℝ) * (t / R) ^ (2 - 1) * (1 / R) = 2 * t / R ^ 2 := by
      norm_num; ring
    rwa [heq] at hadd
  have h2 : HasDerivAt (clamp' R)
      ((0 * (1 + (t / R) ^ 2) - 1 * (2 * t / R ^ 2)) / (1 + (t / R) ^ 2) ^ 2) t :=
    (hasDerivAt_const t (1 : ℝ)).div h1 (by positivity)
  have heq : (0 * (1 + (t / R) ^ 2) - 1 * (2 * t / R ^ 2)) / (1 + (t / R) ^ 2) ^ 2 =
      clamp'' R t := by
    unfold clamp''
    ring
  rwa [heq] at h2

private lemma abs_clamp_le_mul {R : ℝ} (hR : 0 < R) (t : ℝ) :
    |clamp R t| ≤ R * (Real.pi / 2) := by
  unfold clamp
  rw [abs_mul, abs_of_pos hR]
  refine mul_le_mul_of_nonneg_left ?_ hR.le
  exact abs_le.2 ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

private lemma clamp'_nonneg (R t : ℝ) : 0 ≤ clamp' R t := by
  unfold clamp'; positivity

private lemma clamp'_le_one (R t : ℝ) : clamp' R t ≤ 1 := by
  unfold clamp'
  exact (div_le_one (by positivity)).2 (by nlinarith)

private lemma abs_clamp'_le_one (R t : ℝ) : |clamp' R t| ≤ 1 := by
  rw [abs_of_nonneg (clamp'_nonneg R t)]
  exact clamp'_le_one R t

private lemma abs_arctan_le_abs (u : ℝ) : |Real.arctan u| ≤ |u| := by
  have hmono : Monotone (fun t : ℝ => t - Real.arctan t) := by
    refine monotone_of_deriv_nonneg ?_ ?_
    · exact differentiable_id.sub Real.differentiable_arctan
    · intro t
      have hd : HasDerivAt (fun s : ℝ => s - Real.arctan s) (1 - 1 / (1 + t ^ 2)) t :=
        (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
      rw [hd.deriv]
      have hle : 1 / (1 + t ^ 2) ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
      linarith
  rcases le_total 0 u with hu | hu
  · have h1 := hmono hu
    have h2 : 0 ≤ Real.arctan u := by
      simpa [Real.arctan_zero] using Real.arctan_mono hu
    simp only [Real.arctan_zero, sub_zero] at h1
    rw [abs_of_nonneg h2, abs_of_nonneg hu]
    linarith
  · have h1 := hmono hu
    have h2 : Real.arctan u ≤ 0 := by
      simpa [Real.arctan_zero] using Real.arctan_mono hu
    simp only [Real.arctan_zero, sub_zero] at h1
    rw [abs_of_nonpos h2, abs_of_nonpos hu]
    linarith

private lemma abs_clamp_le_abs {R : ℝ} (hR : 0 < R) (t : ℝ) : |clamp R t| ≤ |t| := by
  unfold clamp
  rw [abs_mul, abs_of_pos hR]
  have h := abs_arctan_le_abs (t / R)
  rw [abs_div, abs_of_pos hR] at h
  calc
    R * |Real.arctan (t / R)| ≤ R * (|t| / R) := mul_le_mul_of_nonneg_left h hR.le
    _ = |t| := mul_div_cancel₀ |t| hR.ne'

private lemma abs_clamp''_le {R : ℝ} (hR : 0 < R) (t : ℝ) : |clamp'' R t| ≤ 1 / R := by
  unfold clamp''
  have hden : 0 < (1 + (t / R) ^ 2) ^ 2 := by positivity
  rw [abs_div, abs_neg, abs_of_pos hden, div_le_iff₀ hden]
  have h1 : |2 * t / R ^ 2| = 2 * |t| / R ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (sq_pos_of_pos hR)]
  rw [h1]
  let u := |t| / R
  have hu : 0 ≤ u := by positivity
  have husq : (t / R) ^ 2 = u ^ 2 := by
    simp only [u, div_pow, sq_abs]
  have h2 : 2 * u ≤ (1 + u ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (u - 1), sq_nonneg u]
  have h3 : 2 * |t| / R ^ 2 = (1 / R) * (2 * u) := by
    simp only [u]; field_simp [hR.ne']
  rw [husq, h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

private lemma tendsto_clamp (t : ℝ) :
    Tendsto (fun N : ℕ => clamp ((N : ℝ) + 1) t) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · subst ht
    simp [clamp, Real.arctan_zero]
  · have hslope : Tendsto (fun h : ℝ => h⁻¹ • (Real.arctan (0 + h) - Real.arctan 0))
        (𝓝[≠] 0) (𝓝 1) := by
      have hd : HasDerivAt Real.arctan (1 : ℝ) 0 := by
        simpa using Real.hasDerivAt_arctan 0
      exact hd.tendsto_slope_zero
    have hseq0 : Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul t
      simpa [div_eq_mul_inv] using h
    have hseq : Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq0
        (Eventually.of_forall fun N => div_ne_zero ht (by positivity))
    have hcomp := (hslope.comp hseq).const_mul t
    have hlim : t * (1 : ℝ) = t := mul_one t
    rw [hlim] at hcomp
    refine hcomp.congr fun N => ?_
    have hR : ((N : ℝ) + 1) ≠ 0 := by positivity
    simp only [Function.comp_apply, zero_add, Real.arctan_zero, sub_zero, smul_eq_mul, clamp]
    field_simp [ht, hR]

/-! ### Part 3: Smooth separable composition and its Hessian -/

private noncomputable def coordProj {n : ℕ} (j : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j

private def sepVal {n : ℕ} (q : ℝ) (g : Fin n → ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  q - ∑ j : Fin n, g j (x j)

private noncomputable def sepGrad {n : ℕ} (ψ' : ℝ → ℝ) (q : ℝ) (g g' : Fin n → ℝ → ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin n, (-(ψ' (sepVal q g x) * g' j (x j))) • coordProj j

private noncomputable def sepHessRow {n : ℕ} (ψ' ψ'' : ℝ → ℝ) (q : ℝ) (g g' g'' : Fin n → ℝ → ℝ)
    (j : Fin n) (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (ψ'' (sepVal q g x) * g' j (x j)) • (∑ i : Fin n, g' i (x i) • coordProj i) -
    (ψ' (sepVal q g x) * g'' j (x j)) • coordProj j

private noncomputable def sepHess {n : ℕ} (ψ' ψ'' : ℝ → ℝ) (q : ℝ) (g g' g'' : Fin n → ℝ → ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ∑ j : Fin n, (sepHessRow ψ' ψ'' q g g' g'' j x).smulRight (coordProj j)

private lemma sepVal_hasFDerivAt {n : ℕ} (q : ℝ) (g g' : Fin n → ℝ → ℝ)
    (hg' : ∀ j t, HasDerivAt (g j) (g' j t) t) (x : Fin n → ℝ) :
    HasFDerivAt (sepVal q g) (-∑ j : Fin n, g' j (x j) • coordProj j) x := by
  have hsum : HasFDerivAt (fun y : Fin n → ℝ => ∑ j : Fin n, g j (y j))
      (∑ j : Fin n, g' j (x j) • coordProj j) x := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    exact (hg' j (x j)).comp_hasFDerivAt x (coordProj j).hasFDerivAt
  have hsub := (hasFDerivAt_const q x).sub hsum
  have heq : (0 : (Fin n → ℝ) →L[ℝ] ℝ) - ∑ j : Fin n, g' j (x j) • coordProj j =
      -∑ j : Fin n, g' j (x j) • coordProj j := zero_sub _
  rw [heq] at hsub
  exact hsub

private lemma sepComp_fderiv {n : ℕ} (ψ ψ' : ℝ → ℝ) (q : ℝ) (g g' : Fin n → ℝ → ℝ)
    (hψ' : ∀ t, HasDerivAt ψ (ψ' t) t) (hg' : ∀ j t, HasDerivAt (g j) (g' j t) t) :
    fderiv ℝ (fun x => ψ (sepVal q g x)) = sepGrad ψ' q g g' := by
  ext1 x
  have h1 := (hψ' (sepVal q g x)).comp_hasFDerivAt x (sepVal_hasFDerivAt q g g' hg' x)
  have heq : ψ' (sepVal q g x) • (-∑ j : Fin n, g' j (x j) • coordProj j) =
      sepGrad ψ' q g g' x := by
    ext v
    simp only [sepGrad, _root_.smul_apply, _root_.neg_apply, _root_.sum_apply, smul_eq_mul]
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [heq] at h1
  exact h1.fderiv

private lemma sepGrad_norm_le {n : ℕ} (ψ' : ℝ → ℝ) (q : ℝ) (g g' : Fin n → ℝ → ℝ)
    (hψ'_le : ∀ t, |ψ' t| ≤ 1) (hg'_le : ∀ j t, |g' j t| ≤ 1) (x : Fin n → ℝ) :
    ‖sepGrad ψ' q g g' x‖ ≤ n := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg n) fun v => ?_
  rw [Real.norm_eq_abs]
  simp only [sepGrad, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, coordProj,
    ContinuousLinearMap.proj_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ j : Fin n, |-(ψ' (sepVal q g x) * g' j (x j)) * v j|
        ≤ ∑ _j : Fin n, ‖v‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_neg, abs_mul]
          have h1 : |ψ' (sepVal q g x)| * |g' j (x j)| ≤ 1 := by
            have := mul_le_mul (hψ'_le (sepVal q g x)) (hg'_le j (x j)) (abs_nonneg _) zero_le_one
            linarith
          have hv : |v j| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
          have := mul_le_mul h1 hv (abs_nonneg _) zero_le_one
          linarith
    _ = n * ‖v‖ := by simp

private lemma sepGrad_fderiv {n : ℕ} (ψ' ψ'' : ℝ → ℝ) (q : ℝ) (g g' g'' : Fin n → ℝ → ℝ)
    (hψ'' : ∀ t, HasDerivAt ψ' (ψ'' t) t)
    (hg' : ∀ j t, HasDerivAt (g j) (g' j t) t)
    (hg'' : ∀ j t, HasDerivAt (g' j) (g'' j t) t) (x : Fin n → ℝ) :
    fderiv ℝ (sepGrad ψ' q g g') x = sepHess ψ' ψ'' q g g' g'' x := by
  have hd : HasFDerivAt (sepGrad ψ' q g g') (sepHess ψ' ψ'' q g g' g'' x) x := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have hc : HasFDerivAt (fun y : Fin n → ℝ => -(ψ' (sepVal q g y) * g' j (y j)))
        (sepHessRow ψ' ψ'' q g g' g'' j x) x := by
      have hψu : HasFDerivAt (fun y : Fin n → ℝ => ψ' (sepVal q g y))
          (ψ'' (sepVal q g x) • (-∑ i : Fin n, g' i (x i) • coordProj i)) x :=
        (hψ'' (sepVal q g x)).comp_hasFDerivAt x (sepVal_hasFDerivAt q g g' hg' x)
      have hgj : HasFDerivAt (fun y : Fin n → ℝ => g' j (y j))
          (g'' j (x j) • coordProj j) x :=
        (hg'' j (x j)).comp_hasFDerivAt x (coordProj j).hasFDerivAt
      have hmul := (hψu.mul hgj).neg
      have heq : -(ψ' (sepVal q g x) • (g'' j (x j) • coordProj j) +
          g' j (x j) • (ψ'' (sepVal q g x) • (-∑ i : Fin n, g' i (x i) • coordProj i))) =
          sepHessRow ψ' ψ'' q g g' g'' j x := by
        ext v
        simp only [sepHessRow, _root_.sub_apply, _root_.neg_apply, _root_.add_apply,
          _root_.smul_apply, _root_.sum_apply, smul_eq_mul]
        ring
      rw [heq] at hmul
      exact hmul
    exact hc.smul_const (coordProj j)
  exact hd.fderiv

private lemma sepHess_norm_le {n : ℕ} (ψ' ψ'' : ℝ → ℝ) (q : ℝ) (g g' g'' : Fin n → ℝ → ℝ)
    {Cψ'' Cg'' : ℝ} (hψ'_le : ∀ t, |ψ' t| ≤ 1) (hψ''_le : ∀ t, |ψ'' t| ≤ Cψ'')
    (hCψ'' : 0 ≤ Cψ'') (hg'_le : ∀ j t, |g' j t| ≤ 1) (hg''_le : ∀ j t, |g'' j t| ≤ Cg'')
    (hCg'' : 0 ≤ Cg'') (x : Fin n → ℝ) :
    ‖sepHess ψ' ψ'' q g g' g'' x‖ ≤ n * (Cψ'' * n + Cg'') := by
  have hnonneg : 0 ≤ n * (Cψ'' * n + Cg'') := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hnonneg fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Real.norm_eq_abs]
  simp only [sepHess, sepHessRow, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul, coordProj, ContinuousLinearMap.proj_apply]
  have hsum_v : |∑ i : Fin n, g' i (x i) * v i| ≤ n * ‖v‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ i : Fin n, |g' i (x i) * v i| ≤ ∑ _i : Fin n, ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have hv : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
        have := mul_le_mul (hg'_le i (x i)) hv (abs_nonneg _) zero_le_one
        linarith
      _ = n * ‖v‖ := by simp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ j : Fin n, |((ψ'' (sepVal q g x) * g' j (x j)) * (∑ i : Fin n, g' i (x i) * v i) -
        (ψ' (sepVal q g x) * g'' j (x j)) * v j) * w j|
        ≤ ∑ _j : Fin n, (Cψ'' * n + Cg'') * ‖v‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          have hterm1 : |(ψ'' (sepVal q g x) * g' j (x j)) * (∑ i : Fin n, g' i (x i) * v i)| ≤
              Cψ'' * (n * ‖v‖) := by
            rw [abs_mul, abs_mul]
            have hcoef : |ψ'' (sepVal q g x)| * |g' j (x j)| ≤ Cψ'' := by
              have := mul_le_mul (hψ''_le (sepVal q g x)) (hg'_le j (x j)) (abs_nonneg _) hCψ''
              linarith
            exact mul_le_mul hcoef hsum_v (abs_nonneg _) hCψ''
          have hterm2 : |(ψ' (sepVal q g x) * g'' j (x j)) * v j| ≤ Cg'' * ‖v‖ := by
            rw [abs_mul, abs_mul]
            have hcoef : |ψ' (sepVal q g x)| * |g'' j (x j)| ≤ Cg'' := by
              have := mul_le_mul (hψ'_le (sepVal q g x)) (hg''_le j (x j)) (abs_nonneg _) zero_le_one
              linarith
            have hv : |v j| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
            exact mul_le_mul hcoef hv (abs_nonneg _) hCg''
          have hrow : |(ψ'' (sepVal q g x) * g' j (x j)) * (∑ i : Fin n, g' i (x i) * v i) -
              (ψ' (sepVal q g x) * g'' j (x j)) * v j| ≤ (Cψ'' * n + Cg'') * ‖v‖ := by
            have := (abs_sub _ _).trans (add_le_add hterm1 hterm2)
            linarith
          have hw : |w j| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm w j
          exact mul_le_mul hrow hw (abs_nonneg _) (by positivity)
    _ = n * (Cψ'' * n + Cg'') * ‖v‖ * ‖w‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

private lemma sepHess_offdiag_nonneg {n : ℕ} (ψ' ψ'' : ℝ → ℝ) (q : ℝ) (g g' g'' : Fin n → ℝ → ℝ)
    (hψ''_nonneg : ∀ t, 0 ≤ ψ'' t) (hg'_nonneg : ∀ j t, 0 ≤ g' j t)
    (x : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) :
    0 ≤ (sepHess ψ' ψ'' q g g' g'' x (Pi.single a 1)) (Pi.single b 1) := by
  have heval : (sepHess ψ' ψ'' q g g' g'' x (Pi.single a 1)) (Pi.single b 1) =
      ψ'' (sepVal q g x) * g' b (x b) * g' a (x a) := by
    simp only [sepHess, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
      _root_.smul_apply, smul_eq_mul, coordProj, ContinuousLinearMap.proj_apply]
    rw [Finset.sum_eq_single b]
    · simp only [Pi.single_eq_same, mul_one, sepHessRow, _root_.sub_apply,
        _root_.smul_apply, _root_.sum_apply, smul_eq_mul,
        coordProj, ContinuousLinearMap.proj_apply, Pi.single_eq_of_ne hab.symm, mul_zero,
        sub_zero]
      rw [Finset.sum_eq_single a]
      · simp [mul_assoc]
      · intro i _ hi
        simp [Pi.single_eq_of_ne hi]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [heval]
  exact mul_nonneg (mul_nonneg (hψ''_nonneg _) (hg'_nonneg b _)) (hg'_nonneg a _)

private lemma smooth_separable_comp {n : ℕ} (ψ ψ' ψ'' : ℝ → ℝ) (q : ℝ)
    (g g' g'' : Fin n → ℝ → ℝ) {B C Cψ'' Cg'' : ℝ}
    (hψ_cd : ContDiff ℝ 2 ψ)
    (hψ' : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ'' : ∀ t, HasDerivAt ψ' (ψ'' t) t)
    (hψ_bdd : ∀ u, |u| ≤ |q| + n * B → |ψ u| ≤ C)
    (hψ'_le : ∀ t, |ψ' t| ≤ 1)
    (hψ''_nonneg : ∀ t, 0 ≤ ψ'' t)
    (hψ''_le : ∀ t, |ψ'' t| ≤ Cψ'')
    (hCψ'' : 0 ≤ Cψ'')
    (hg_cd : ∀ j, ContDiff ℝ 2 (g j))
    (hg' : ∀ j t, HasDerivAt (g j) (g' j t) t)
    (hg'' : ∀ j t, HasDerivAt (g' j) (g'' j t) t)
    (hg_bdd : ∀ j t, |g j t| ≤ B)
    (hg'_nonneg : ∀ j t, 0 ≤ g' j t)
    (hg'_le : ∀ j t, |g' j t| ≤ 1)
    (hg''_le : ∀ j t, |g'' j t| ≤ Cg'')
    (hCg'' : 0 ≤ Cg'') :
    let f : (Fin n → ℝ) → ℝ := fun x => ψ (q - ∑ j : Fin n, g j (x j))
    ContDiff ℝ 2 f ∧
      (∀ x, ‖f x‖ ≤ C) ∧
      (∀ x, ‖fderiv ℝ f x‖ ≤ n) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ n * (Cψ'' * n + Cg'')) ∧
      (∀ x (a b : Fin n), a ≠ b →
        0 ≤ (fderiv ℝ (fderiv ℝ f) x (Pi.single a 1)) (Pi.single b 1)) := by
  intro f
  have hf_eq : f = fun x => ψ (sepVal q g x) := rfl
  have hf_cd : ContDiff ℝ 2 f := by
    refine hψ_cd.comp (contDiff_const.sub ?_)
    refine ContDiff.sum fun j _ => (hg_cd j).comp (coordProj j).contDiff
  have hf_bdd : ∀ x, ‖f x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs]
    refine hψ_bdd (sepVal q g x) ?_
    calc
      |sepVal q g x| = |q - ∑ j : Fin n, g j (x j)| := rfl
      _ ≤ |q| + |∑ j : Fin n, g j (x j)| := abs_sub _ _
      _ ≤ |q| + ∑ j : Fin n, |g j (x j)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ |q| + ∑ _j : Fin n, B := by
          gcongr with j
          exact hg_bdd j (x j)
      _ = |q| + n * B := by simp
  have hfd : fderiv ℝ f = sepGrad ψ' q g g' := by
    rw [hf_eq]
    exact sepComp_fderiv ψ ψ' q g g' hψ' hg'
  have hfdd : ∀ x, fderiv ℝ (fderiv ℝ f) x = sepHess ψ' ψ'' q g g' g'' x := fun x => by
    rw [hfd]
    exact sepGrad_fderiv ψ' ψ'' q g g' g'' hψ'' hg' hg'' x
  refine ⟨hf_cd, hf_bdd, fun x => ?_, fun x => ?_, fun x a b hab => ?_⟩
  · rw [hfd]; exact sepGrad_norm_le ψ' q g g' hψ'_le hg'_le x
  · rw [hfdd]; exact sepHess_norm_le ψ' ψ'' q g g' g'' hψ'_le hψ''_le hCψ'' hg'_le hg''_le hCg'' x
  · rw [hfdd]; exact sepHess_offdiag_nonneg ψ' ψ'' q g g' g'' hψ''_nonneg hg'_nonneg x a b hab

/-! ### Part 4: Coordinatewise smooth approximation of `max (Q k - Ds M Q x k) 0` -/

private noncomputable def coordTerm {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (k : Fin n)
    (R ε : ℝ) (j : Fin n) : ℝ → ℝ :=
  if j = k then clamp R else fun t => M.a j k * softplus ε (clamp R t - Q j)

private noncomputable def coordTerm' {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (k : Fin n)
    (R ε : ℝ) (j : Fin n) : ℝ → ℝ :=
  if j = k then clamp' R else fun t => M.a j k * (softplus' ε (clamp R t - Q j) * clamp' R t)

private noncomputable def coordTerm'' {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (k : Fin n)
    (R ε : ℝ) (j : Fin n) : ℝ → ℝ :=
  if j = k then clamp'' R
  else fun t => M.a j k * (softplus'' ε (clamp R t - Q j) * clamp' R t * clamp' R t +
    softplus' ε (clamp R t - Q j) * clamp'' R t)

private lemma coordTerm_props {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (k : Fin n)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (j : Fin n) :
    ContDiff ℝ 2 (coordTerm M Q k R ε j) ∧
      (∀ t, HasDerivAt (coordTerm M Q k R ε j) (coordTerm' M Q k R ε j t) t) ∧
      (∀ t, HasDerivAt (coordTerm' M Q k R ε j) (coordTerm'' M Q k R ε j t) t) ∧
      (∀ t, |coordTerm M Q k R ε j t| ≤ R * (Real.pi / 2) + (∑ i : Fin n, |Q i|) + ε * Real.log 2) ∧
      (∀ t, 0 ≤ coordTerm' M Q k R ε j t) ∧
      (∀ t, |coordTerm' M Q k R ε j t| ≤ 1) ∧
      (∀ t, |coordTerm'' M Q k R ε j t| ≤ 1 / ε + 1 / R) := by
  by_cases hj : j = k
  · subst hj
    simp only [coordTerm, coordTerm', coordTerm'', ↓reduceIte]
    refine ⟨clamp_contDiff R, hasDerivAt_clamp hR, hasDerivAt_clamp' R, ?_, clamp'_nonneg R,
      abs_clamp'_le_one R, ?_⟩
    · intro t
      have h1 := abs_clamp_le_mul hR t
      have h2 : 0 ≤ ∑ i : Fin n, |Q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have h3 : 0 ≤ ε * Real.log 2 := mul_nonneg hε.le (Real.log_nonneg (by norm_num))
      linarith
    · intro t
      have h1 := abs_clamp''_le hR t
      have h2 : 0 ≤ 1 / ε := by positivity
      linarith
  · simp only [coordTerm, coordTerm', coordTerm'', hj, ↓reduceIte]
    have ha0 : 0 ≤ M.a j k := M.a_nonneg j k
    have ha1 : M.a j k ≤ 1 := M.a_le_one j k
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact contDiff_const.mul (softplus_contDiff.comp ((clamp_contDiff R).sub contDiff_const))
    · intro t
      have hc := (hasDerivAt_clamp hR t).sub_const (Q j)
      have hs := ((hasDerivAt_softplus hε (clamp R t - Q j)).comp t hc).const_mul (M.a j k)
      exact hs
    · intro t
      have hc := (hasDerivAt_clamp hR t).sub_const (Q j)
      have hsp := (hasDerivAt_softplus' hε (clamp R t - Q j)).comp t hc
      have hcp := hasDerivAt_clamp' R t
      exact (hsp.mul hcp).const_mul (M.a j k)
    · intro t
      rw [abs_mul, abs_of_nonneg ha0]
      have hs : |softplus ε (clamp R t - Q j)| ≤ R * (Real.pi / 2) + (∑ i : Fin n, |Q i|) + ε * Real.log 2 := by
        have h1 := abs_softplus_le hε (clamp R t - Q j)
        have h2 : |clamp R t - Q j| ≤ |clamp R t| + |Q j| := abs_sub _ _
        have h3 := abs_clamp_le_mul hR t
        have h4 : |Q j| ≤ ∑ i : Fin n, |Q i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (Q i)) (Finset.mem_univ j)
        linarith
      have hnonneg : 0 ≤ R * (Real.pi / 2) + (∑ i : Fin n, |Q i|) + ε * Real.log 2 := by
        have h1 : 0 ≤ R * (Real.pi / 2) := by positivity
        have h2 : 0 ≤ ∑ i : Fin n, |Q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have h3 : 0 ≤ ε * Real.log 2 := mul_nonneg hε.le (Real.log_nonneg (by norm_num))
        linarith
      calc
        M.a j k * |softplus ε (clamp R t - Q j)|
            ≤ 1 * (R * (Real.pi / 2) + (∑ i : Fin n, |Q i|) + ε * Real.log 2) :=
              mul_le_mul ha1 hs (abs_nonneg _) zero_le_one
        _ = R * (Real.pi / 2) + (∑ i : Fin n, |Q i|) + ε * Real.log 2 := one_mul _
    · intro t
      exact mul_nonneg ha0 (mul_nonneg (softplus'_nonneg ε _) (clamp'_nonneg R t))
    · intro t
      rw [abs_mul, abs_of_nonneg ha0, abs_mul]
      have h1 : |softplus' ε (clamp R t - Q j)| * |clamp' R t| ≤ 1 := by
        have := mul_le_mul (abs_softplus'_le_one ε (clamp R t - Q j)) (abs_clamp'_le_one R t)
          (abs_nonneg _) zero_le_one
        simpa using this
      have := mul_le_mul ha1 h1 (by positivity) zero_le_one
      simpa using this
    · intro t
      rw [abs_mul, abs_of_nonneg ha0]
      have hinner : |softplus'' ε (clamp R t - Q j) * clamp' R t * clamp' R t +
          softplus' ε (clamp R t - Q j) * clamp'' R t| ≤ 1 / ε + 1 / R := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul]
          have h1 : |softplus'' ε (clamp R t - Q j)| * |clamp' R t| ≤ 1 / ε := by
            have := mul_le_mul (abs_softplus''_le hε (clamp R t - Q j)) (abs_clamp'_le_one R t)
              (abs_nonneg _) (by positivity)
            simpa using this
          have := mul_le_mul h1 (abs_clamp'_le_one R t) (abs_nonneg _) (by positivity)
          simpa using this
        · rw [abs_mul]
          have := mul_le_mul (abs_softplus'_le_one ε (clamp R t - Q j)) (abs_clamp''_le hR t)
            (abs_nonneg _) zero_le_one
          simpa using this
      have := mul_le_mul ha1 hinner (abs_nonneg _) zero_le_one
      simpa using this

private lemma normalLaw_isProb {n : ℕ} (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    IsProbabilityMeasure (normalLaw m S) := by
  unfold normalLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

private lemma integrable_coord {n : ℕ} (m : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) : Integrable (fun x : Fin n → ℝ => x k) (normalLaw m S) := by
  unfold normalLaw
  refine (integrable_map_measure (g := fun x : Fin n → ℝ => x k)
    (Continuous.aestronglyMeasurable (by fun_prop)) (by fun_prop)).2 ?_
  exact IsGaussian.integrable_dual (multivariateGaussian (WithLp.toLp 2 m) S)
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)

private lemma integral_shortage_le {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hdiag : ∀ k, S₁ k k = S₂ k k) (hle : ∀ k l, S₁ k l ≤ S₂ k l)
    (Q : Fin n → ℝ) (k : Fin n) :
    ∫ x, max (Q k - Ds M Q x k) 0 ∂(normalLaw m S₁) ≤
      ∫ x, max (Q k - Ds M Q x k) 0 ∂(normalLaw m S₂) := by
  let f : ℕ → (Fin n → ℝ) → ℝ := fun N x =>
    softplus (1 / ((N : ℝ) + 1))
      (Q k - ∑ j : Fin n, coordTerm M Q k ((N : ℝ) + 1) (1 / ((N : ℝ) + 1)) j (x j))
  have hstep : ∀ N : ℕ,
      ∫ x, f N x ∂(normalLaw m S₁) ≤ ∫ x, f N x ∂(normalLaw m S₂) := by
    intro N
    set R : ℝ := (N : ℝ) + 1
    set ε : ℝ := 1 / ((N : ℝ) + 1)
    have hR : 0 < R := by positivity
    have hε : 0 < ε := by positivity
    set B : ℝ := R * (Real.pi / 2) + (∑ i : Fin n, |Q i|) + ε * Real.log 2
    set C : ℝ := |Q k| + n * B + ε * Real.log 2
    have hprops := fun j => coordTerm_props M Q k hR hε j
    have hcomp := smooth_separable_comp (softplus ε) (softplus' ε) (softplus'' ε) (Q k)
      (coordTerm M Q k R ε) (coordTerm' M Q k R ε) (coordTerm'' M Q k R ε)
      (B := B) (C := C) (Cψ'' := 1 / ε) (Cg'' := 1 / ε + 1 / R)
      softplus_contDiff
      (hasDerivAt_softplus hε)
      (hasDerivAt_softplus' hε)
      (fun u hu => (abs_softplus_le hε u).trans (by linarith))
      (abs_softplus'_le_one ε)
      (softplus''_nonneg hε)
      (abs_softplus''_le hε)
      (by positivity)
      (fun j => (hprops j).1)
      (fun j => (hprops j).2.1)
      (fun j => (hprops j).2.2.1)
      (fun j => (hprops j).2.2.2.1)
      (fun j => (hprops j).2.2.2.2.1)
      (fun j => (hprops j).2.2.2.2.2.1)
      (fun j => (hprops j).2.2.2.2.2.2)
      (by positivity)
    exact muller_scarsini_normal_smooth_bounded m S₁ S₂ hS₁ hS₂ hdiag hle (f N)
      hcomp.1 hcomp.2.1 hcomp.2.2.1 hcomp.2.2.2.1 hcomp.2.2.2.2
  let bound : (Fin n → ℝ) → ℝ := fun x =>
    |Q k| + Real.log 2 + ∑ j : Fin n, (|x j| + |Q j| + Real.log 2)
  have hbound : ∀ N : ℕ, ∀ x : Fin n → ℝ, ‖f N x‖ ≤ bound x := by
    intro N x
    set R : ℝ := (N : ℝ) + 1
    set ε : ℝ := 1 / ((N : ℝ) + 1)
    have hR : 0 < R := by positivity
    have hε : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := (div_le_one hR).2 (by linarith [Nat.cast_nonneg (α := ℝ) N])
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [Real.norm_eq_abs]
    have h1 := abs_softplus_le hε (Q k - ∑ j : Fin n, coordTerm M Q k R ε j (x j))
    have h2 : |Q k - ∑ j : Fin n, coordTerm M Q k R ε j (x j)| ≤
        |Q k| + ∑ j : Fin n, |coordTerm M Q k R ε j (x j)| :=
      (abs_sub _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have h3 : ∀ j : Fin n, |coordTerm M Q k R ε j (x j)| ≤ |x j| + |Q j| + Real.log 2 := by
      intro j
      by_cases hj : j = k
      · simp only [coordTerm, hj, ↓reduceIte]
        have := abs_clamp_le_abs hR (x k)
        linarith [abs_nonneg (Q k)]
      · simp only [coordTerm, hj, ↓reduceIte]
        rw [abs_mul, abs_of_nonneg (M.a_nonneg j k)]
        have ha : M.a j k ≤ 1 := M.a_le_one j k
        have hs := abs_softplus_le hε (clamp R (x j) - Q j)
        have hc : |clamp R (x j) - Q j| ≤ |x j| + |Q j| :=
          (abs_sub _ _).trans (add_le_add (abs_clamp_le_abs hR (x j)) le_rfl)
        have hεl : ε * Real.log 2 ≤ Real.log 2 := by nlinarith
        have hsum : |softplus ε (clamp R (x j) - Q j)| ≤ |x j| + |Q j| + Real.log 2 := by linarith
        have := mul_le_mul ha hsum (abs_nonneg _) zero_le_one
        simpa using this
    have h4 : ∑ j : Fin n, |coordTerm M Q k R ε j (x j)| ≤
        ∑ j : Fin n, (|x j| + |Q j| + Real.log 2) :=
      Finset.sum_le_sum fun j _ => h3 j
    have hεl : ε * Real.log 2 ≤ Real.log 2 := by nlinarith
    simp only [bound]
    linarith
  have hlim : ∀ x : Fin n → ℝ,
      Tendsto (fun N : ℕ => f N x) atTop (𝓝 (max (Q k - Ds M Q x k) 0)) := by
    intro x
    have hcoord : ∀ j : Fin n,
        Tendsto (fun N : ℕ => coordTerm M Q k ((N : ℝ) + 1) (1 / ((N : ℝ) + 1)) j (x j))
          atTop (𝓝 (if j = k then x k else M.a j k * max (x j - Q j) 0)) := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [coordTerm, ↓reduceIte]
        exact tendsto_clamp (x j)
      · simp only [coordTerm, hj, ↓reduceIte]
        exact (tendsto_softplus ((tendsto_clamp (x j)).sub_const (Q j))).const_mul (M.a j k)
    have hsum : Tendsto
        (fun N : ℕ => ∑ j : Fin n, coordTerm M Q k ((N : ℝ) + 1) (1 / ((N : ℝ) + 1)) j (x j))
        atTop (𝓝 (Ds M Q x k)) := by
      have ht := tendsto_finsetSum Finset.univ fun j _ => hcoord j
      convert ht using 2
      unfold Ds
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
      simp only [↓reduceIte]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : j ≠ k := (Finset.mem_erase.1 hj).1
      simp [hne]
    exact tendsto_softplus (tendsto_const_nhds.sub hsum)
  have htendsto : ∀ S : Matrix (Fin n) (Fin n) ℝ,
      Tendsto (fun N : ℕ => ∫ x, f N x ∂(normalLaw m S)) atTop
        (𝓝 (∫ x, max (Q k - Ds M Q x k) 0 ∂(normalLaw m S))) := by
    intro S
    have : IsProbabilityMeasure (normalLaw m S) := normalLaw_isProb m S
    have hmeas : ∀ N : ℕ, AEStronglyMeasurable (f N) (normalLaw m S) := by
      intro N
      set R : ℝ := (N : ℝ) + 1
      set ε : ℝ := 1 / ((N : ℝ) + 1)
      have hR : 0 < R := by positivity
      have hε : 0 < ε := by positivity
      have hcont : Continuous (f N) := by
        refine softplus_contDiff.continuous.comp (continuous_const.sub ?_)
        refine continuous_finsetSum _ fun j _ => ?_
        exact (coordTerm_props M Q k hR hε j).1.continuous.comp (continuous_apply j)
      exact hcont.aestronglyMeasurable
    have hbind : Integrable bound (normalLaw m S) := by
      refine (integrable_const _).add (integrable_finsetSum _ fun j _ => ?_)
      exact (((integrable_coord m S j).norm).add (integrable_const _)).add (integrable_const _)
    exact tendsto_integral_of_dominated_convergence bound hmeas hbind
      (fun N => Eventually.of_forall (hbound N))
      (Eventually.of_forall hlim)
  exact le_of_tendsto_of_tendsto (htendsto S₁) (htendsto S₂) (Eventually.of_forall hstep)

/-! ### Part 5: Main theorem (`Proposition 2` of Netessine & Rudi) -/

private lemma firmProfitAt_eq_sub_shortage {n : ℕ} (M : Model n) (Q : Fin n → ℝ)
    (x : Fin n → ℝ) (k : Fin n) :
    firmProfitAt M Q x k = M.u k * Q k - (M.u k + M.o k) * max (Q k - Ds M Q x k) 0 := by
  unfold firmProfitAt
  rcases le_total (Ds M Q x k) (Q k) with h | h
  · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]
    ring
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]
    ring

private lemma integrable_shortage {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → ℝ) (k : Fin n) :
    Integrable (fun x => max (Q k - Ds M Q x k) 0) (normalLaw m S) := by
  have := normalLaw_isProb m S
  have hc := integrable_coord m S
  have hDs : Integrable (fun x => Ds M Q x k) (normalLaw m S) := by
    unfold Ds
    refine (hc k).add (integrable_finsetSum _ fun j _ => ?_)
    exact ((((hc j).sub (integrable_const _)).sup (integrable_const _))).const_mul _
  exact ((integrable_const _).sub hDs).sup (integrable_const _)

theorem solution {n : ℕ} (M : Model n) (m : Fin n → ℝ)
    (S₁ S₂ : Matrix (Fin n) (Fin n) ℝ) (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (i j : Fin n) (hraise : RaisesCovariance S₁ S₂ i j) :
    (∀ Q : Fin n → ℝ, (∀ k, 0 ≤ Q k) → centralProfit M m S₂ Q ≤ centralProfit M m S₁ Q) ∧
      ∀ Q₁ Q₂ : Fin n → ℝ, IsCentralOptimal M m S₁ Q₁ → IsCentralOptimal M m S₂ Q₂ →
        centralProfit M m S₂ Q₂ ≤ centralProfit M m S₁ Q₁ := by
  obtain ⟨hij, hle_ij, hS₂sym, hS₁sym, hrest⟩ := hraise
  have hdiag : ∀ k, S₁ k k = S₂ k k := by
    intro k
    apply hrest
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hij (h1.symm.trans h2)
    · exact hij (h2.symm.trans h1)
  have hle : ∀ k l, S₁ k l ≤ S₂ k l := by
    intro k l
    by_cases h : (k = i ∧ l = j) ∨ (k = j ∧ l = i)
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hle_ij
      · rw [hS₁sym, hS₂sym]; exact hle_ij
    · exact le_of_eq (hrest k l h)
  have part1 : ∀ Q : Fin n → ℝ, (∀ k, 0 ≤ Q k) →
      centralProfit M m S₂ Q ≤ centralProfit M m S₁ Q := by
    intro Q _hQ
    have := normalLaw_isProb m S₁
    have := normalLaw_isProb m S₂
    have hfirm_int : ∀ S : Matrix (Fin n) (Fin n) ℝ, ∀ k : Fin n,
        Integrable (fun x => firmProfitAt M Q x k) (normalLaw m S) := by
      intro S k
      have := normalLaw_isProb m S
      have heq : (fun x => firmProfitAt M Q x k) =
          fun x => M.u k * Q k - (M.u k + M.o k) * max (Q k - Ds M Q x k) 0 :=
        funext fun x => firmProfitAt_eq_sub_shortage M Q x k
      rw [heq]
      exact (integrable_const _).sub ((integrable_shortage M m S Q k).const_mul _)
    unfold centralProfit profitAt
    rw [integral_finsetSum Finset.univ fun k _ => hfirm_int S₂ k,
      integral_finsetSum Finset.univ fun k _ => hfirm_int S₁ k]
    refine Finset.sum_le_sum fun k _ => ?_
    have hrewrite : ∀ S : Matrix (Fin n) (Fin n) ℝ,
        ∫ x, firmProfitAt M Q x k ∂(normalLaw m S) =
          M.u k * Q k - (M.u k + M.o k) * ∫ x, max (Q k - Ds M Q x k) 0 ∂(normalLaw m S) := by
      intro S
      have := normalLaw_isProb m S
      have heq : (fun x => firmProfitAt M Q x k) =
          fun x => M.u k * Q k - (M.u k + M.o k) * max (Q k - Ds M Q x k) 0 :=
        funext fun x => firmProfitAt_eq_sub_shortage M Q x k
      rw [heq, integral_sub (integrable_const _) ((integrable_shortage M m S Q k).const_mul _),
        integral_const, probReal_univ, one_smul, integral_const_mul]
    rw [hrewrite S₂, hrewrite S₁]
    have hwo : 0 ≤ M.u k + M.o k := by
      unfold Model.u Model.o
      linarith [M.c_lt_r k, M.s_lt_c k]
    have hshort := integral_shortage_le M m S₁ S₂ hS₁ hS₂ hdiag hle Q k
    nlinarith
  refine ⟨part1, ?_⟩
  intro Q₁ Q₂ h1 h2
  exact (part1 Q₂ h2.1).trans (h1.2 Q₂ h2.1)
