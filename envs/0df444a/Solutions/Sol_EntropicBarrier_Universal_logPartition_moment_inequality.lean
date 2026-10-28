-- Prove2me | solution 1 for EntropicBarrier.Universal.logPartition_moment_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T04:04:12.836535+00:00
-- url     : https://prove2.me/submissions/7ecede90-b14b-4d1a-99dc-a00ed6e2bf9a

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Theorems.Thm_ConvexOptimization_prekopa_marginal_log_concave
import Theorems.Thm_EntropicBarrier_Universal_lemma2_third_moment

set_option autoImplicit false

open scoped RealInnerProductSpace
open MeasureTheory Filter Topology

namespace EBMI

open EntropicBarrier.Universal ConvexOptimization

/-! ## Log-concavity toolkit (rpow form of `ConvexOptimization.LogConcaveOn`) -/

theorem lc_ind {E : Type*} [AddCommGroup E] [Module ℝ E] (C : Set E) (hC : Convex ℝ C)
    (g : E → ℝ) (hg0 : ∀ x, 0 < g x)
    (hg : ∀ x y : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g x ^ a * g y ^ b ≤ g (a • x + b • y)) :
    LogConcaveOn Set.univ (C.indicator g) := by
  refine ⟨fun x _ => Set.indicator_nonneg (fun y _ => (hg0 y).le) x, ?_⟩
  intro x _ y _ a b ha hb hab
  have hnn : ∀ z, 0 ≤ C.indicator g z := fun z => Set.indicator_nonneg (fun y _ => (hg0 y).le) z
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simp
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simp
  by_cases hx : x ∈ C
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        Set.indicator_of_mem (hC hx hy ha hb hab)]
      exact hg x y a b ha hb hab
    · rw [Set.indicator_of_notMem hy, Real.zero_rpow hb0.ne', mul_zero]
      exact hnn _
  · rw [Set.indicator_of_notMem hx, Real.zero_rpow ha0.ne', zero_mul]
    exact hnn _

theorem lc_mul {E : Type*} [AddCommGroup E] [Module ℝ E] (f g : E → ℝ)
    (hf : LogConcaveOn Set.univ f) (hg : LogConcaveOn Set.univ g) :
    LogConcaveOn Set.univ (fun x => f x * g x) := by
  refine ⟨fun x hx => mul_nonneg (hf.1 x hx) (hg.1 x hx), ?_⟩
  intro x hx y hy a b ha hb hab
  simp only
  rw [Real.mul_rpow (hf.1 x hx) (hg.1 x hx), Real.mul_rpow (hf.1 y hy) (hg.1 y hy)]
  calc f x ^ a * g x ^ a * (f y ^ b * g y ^ b) = (f x ^ a * f y ^ b) * (g x ^ a * g y ^ b) := by
        ring
    _ ≤ f (a • x + b • y) * g (a • x + b • y) :=
        mul_le_mul (hf.2 x hx y hy a b ha hb hab) (hg.2 x hx y hy a b ha hb hab)
          (mul_nonneg (Real.rpow_nonneg (hg.1 x hx) _) (Real.rpow_nonneg (hg.1 y hy) _))
          (hf.1 _ (Set.mem_univ _))

theorem lc_comp {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : F → ℝ) (hf : LogConcaveOn Set.univ f) (A : E → F)
    (hA : ∀ x y : E, ∀ a b : ℝ, a + b = 1 → A (a • x + b • y) = a • A x + b • A y) :
    LogConcaveOn Set.univ (f ∘ A) := by
  refine ⟨fun x _ => hf.1 (A x) (Set.mem_univ _), ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [Function.comp, hA x y a b hab]
  exact hf.2 _ (Set.mem_univ _) _ (Set.mem_univ _) a b ha hb hab

/-! ## The density of `p_θ` (copied from our gated reduction d1be0a34) -/

noncomputable def F0 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  ∫ x in K, Real.exp (s * ⟪θ, x⟫)

theorem volume_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    0 < volume K :=
  (isOpen_interior.measure_pos volume hK.2.2).trans_le (measure_mono interior_subset)

theorem F0_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (s : ℝ) : 0 < F0 K θ s := by
  unfold F0
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (s * ⟪θ, x⟫)) := by
    fun_prop
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (hc.continuousOn.integrableOn_compact hK.1)]
  have : Function.support (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (s * ⟪θ, x⟫)) =
      Set.univ := by
    ext x; simp [(Real.exp_pos _).ne']
  rw [this, Measure.restrict_apply_univ]
  exact volume_pos hK

theorem integral_expFamily' {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, g x ∂(expFamily K θ) = (F0 K θ 1)⁻¹ * ∫ x in K, Real.exp ⟪θ, x⟫ * g x := by
  have hZ : logPartition K θ = Real.log (F0 K θ 1) := by
    unfold logPartition F0; simp only [one_mul]
  unfold expFamily
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top), ← integral_const_mul]
  congr 1; ext x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, Real.exp_sub, hZ,
    Real.exp_log (F0_pos hK θ 1)]
  ring

theorem isProb {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (expFamily K θ) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (⟪θ, x⟫ - logPartition K θ)) := by fun_prop
  have hfin : IsFiniteMeasure (expFamily K θ) := by
    unfold expFamily
    exact isFiniteMeasure_withDensity_ofReal
      (hc.continuousOn.integrableOn_compact hK.1).hasFiniteIntegral
  have h1 := integral_expFamily' hK θ (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  have hF : F0 K θ 1 = ∫ x in K, Real.exp ⟪θ, x⟫ := by unfold F0; simp only [one_mul]
  rw [← hF, inv_mul_cancel₀ (F0_pos hK θ 1).ne'] at h1
  refine ⟨?_⟩
  rw [measureReal_def] at h1
  exact (ENNReal.toReal_eq_one_iff _).1 h1

/-- The Lebesgue density of `p_θ`. -/
noncomputable def Fd {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  K.indicator (fun y => Real.exp (⟪θ, y⟫ - logPartition K θ)) y

theorem Fd_nn {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (θ y : EuclideanSpace ℝ (Fin n)) :
    0 ≤ Fd K θ y :=
  Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) y

theorem measurable_Fd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : Measurable (Fd K θ) :=
  Measurable.indicator (by fun_prop) hK.1.measurableSet

theorem int_mu {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : EuclideanSpace ℝ (Fin n) → E') :
    ∫ x, g x ∂(expFamily K θ) = ∫ x, Fd K θ x • g x := by
  unfold expFamily
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
    ← integral_indicator hK.1.measurableSet]
  congr 1; ext x
  unfold Fd
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]

theorem intF {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (G : EuclideanSpace ℝ (Fin n) → E') (hG : Continuous G) :
    Integrable (fun y => Fd K θ y • G y) := by
  have e : (fun y => Fd K θ y • G y) =
      K.indicator (fun y => Real.exp (⟪θ, y⟫ - logPartition K θ) • G y) := by
    ext y; unfold Fd
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_smul]
  rw [e]
  exact (integrable_indicator_iff hK.1.measurableSet).2
    ((by fun_prop : Continuous fun y => Real.exp (⟪θ, y⟫ - logPartition K θ) • G y)
      |>.continuousOn.integrableOn_compact hK.1)

theorem intF' {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : Continuous G) :
    Integrable (fun y => Fd K θ y * G y) := intF hK θ G hG

theorem intFd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : Integrable (Fd K θ) :=
  (intF' hK θ (fun _ => (1 : ℝ)) continuous_const).congr (Eventually.of_forall fun y => mul_one _)

theorem lc_Fd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : LogConcaveOn Set.univ (Fd K θ) := by
  refine lc_ind K hK.2.1 _ (fun _ => Real.exp_pos _) ?_
  intro x y a b ha hb hab
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply le_of_eq
  congr 1
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  linear_combination (-logPartition K θ) * hab

theorem integral_Fd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : ∫ y, Fd K θ y = 1 := by
  have := isProb hK θ
  have h := int_mu hK θ (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one, probReal_univ] at h
  exact h.symm

/-- The centred linear functional `φ(y) = ⟪y - x(θ), h⟫`. -/
noncomputable def phi {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ h : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪y - meanMap K θ, h⟫

theorem continuous_phi {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ h : EuclideanSpace ℝ (Fin n)) : Continuous (phi K θ h) := by
  unfold phi; fun_prop

theorem centred {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) : ∫ y, Fd K θ y * phi K θ h y = 0 := by
  have hm : meanMap K θ = ∫ y, Fd K θ y • y := by unfold meanMap; exact int_mu hK θ id
  have e : ∀ y, Fd K θ y * phi K θ h y =
      ⟪h, Fd K θ y • y⟫ - ⟪h, meanMap K θ⟫ * Fd K θ y := by
    intro y; unfold phi
    rw [real_inner_smul_right, inner_sub_left, real_inner_comm h y,
      real_inner_comm h (meanMap K θ)]
    ring
  have i1 := intF hK θ (fun y => y) continuous_id
  rw [integral_congr_ae (Eventually.of_forall e),
    integral_sub (i1.const_inner h) ((intFd hK θ).const_mul ⟪h, meanMap K θ⟫),
    integral_inner i1, integral_const_mul, integral_Fd hK θ, ← hm]
  ring

/-! ## The uniform smoothing kernel -/

noncomputable def psi (ε t : ℝ) : ℝ := (Set.Icc (-ε) ε).indicator (fun _ => (2 * ε)⁻¹) t

theorem psi_nn (ε : ℝ) (hε : 0 < ε) (t : ℝ) : 0 ≤ psi ε t :=
  Set.indicator_nonneg (fun _ _ => by positivity) t

theorem psi_le (ε : ℝ) (hε : 0 < ε) (t : ℝ) : psi ε t ≤ (2 * ε)⁻¹ := by
  unfold psi
  by_cases ht : t ∈ Set.Icc (-ε) ε
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]; positivity

theorem measurable_psi (ε : ℝ) : Measurable (psi ε) :=
  measurable_const.indicator measurableSet_Icc

theorem lc_psi (ε : ℝ) (hε : 0 < ε) : LogConcaveOn Set.univ (psi ε) := by
  refine lc_ind _ (convex_Icc _ _) _ (fun _ => by positivity) ?_
  intro x y a b ha hb hab
  rw [← Real.rpow_add (by positivity), hab, Real.rpow_one]

theorem psi_moment (ε : ℝ) (hε : 0 < ε) (c : ℝ) (k : ℕ) :
    ∫ t, t ^ k * psi ε (t - c) =
      (2 * ε)⁻¹ * (((c + ε) ^ (k + 1) - (c - ε) ^ (k + 1)) / (k + 1)) := by
  have e : ∀ t, t ^ k * psi ε (t - c) =
      (Set.Icc (c - ε) (c + ε)).indicator (fun t => (2 * ε)⁻¹ * t ^ k) t := by
    intro t; unfold psi
    by_cases ht : t ∈ Set.Icc (c - ε) (c + ε)
    · have h' : t - c ∈ Set.Icc (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [Set.indicator_of_mem h', Set.indicator_of_mem ht]; ring
    · have h' : t - c ∉ Set.Icc (-ε) ε := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem ht, mul_zero]
  rw [integral_congr_ae (Eventually.of_forall e), integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const_mul, integral_pow]

/-! ## The smoothed marginal and its moments -/

/-- Density of `φ(X) + Z`, `X ∼ p_θ`, `Z ∼ U[-ε, ε]` independent. -/
noncomputable def dens {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ h : EuclideanSpace ℝ (Fin n)) (ε t : ℝ) : ℝ :=
  ∫ y, Fd K θ y * psi ε (t - phi K θ h y)

theorem hprod {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    Integrable (Function.uncurry fun (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) =>
      t ^ k * (Fd K θ y * psi ε (t - phi K θ h y))) (volume.prod volume) := by
  obtain ⟨M, hM⟩ := hK.1.exists_bound_of_continuousOn (continuous_phi K θ h).continuousOn
  set R := |M| + ε with hR
  have hR0 : 0 ≤ R := by positivity
  have hB : Integrable (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (Set.Icc (-R) R).indicator (fun _ => R ^ k) z.1 * (Fd K θ z.2 * (2 * ε)⁻¹))
      (volume.prod volume) :=
    Integrable.mul_prod ((continuous_const.integrableOn_Icc).integrable_indicator
      measurableSet_Icc) (intF' hK θ (fun _ => (2 * ε)⁻¹) continuous_const)
  refine hB.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (((measurable_fst.pow_const k).mul (((measurable_Fd hK θ).comp measurable_snd).mul
      ((measurable_psi ε).comp (measurable_fst.sub
        ((continuous_phi K θ h).measurable.comp measurable_snd)))))).aestronglyMeasurable
  obtain ⟨t, y⟩ := z
  simp only [Function.uncurry_apply_pair]
  have hrhs : 0 ≤ (Set.Icc (-R) R).indicator (fun _ => R ^ k) t * (Fd K θ y * (2 * ε)⁻¹) :=
    mul_nonneg (Set.indicator_nonneg (fun _ _ => pow_nonneg hR0 k) t)
      (mul_nonneg (Fd_nn K θ y) (by positivity))
  by_cases hy : y ∈ K
  · by_cases ht : t - phi K θ h y ∈ Set.Icc (-ε) ε
    · have hphi : |phi K θ h y| ≤ |M| := (Real.norm_eq_abs _ ▸ hM y hy).trans (le_abs_self M)
      have htR : |t| ≤ R := by
        have := abs_le.2 ⟨ht.1, ht.2⟩
        calc |t| = |(t - phi K θ h y) + phi K θ h y| := by ring_nf
          _ ≤ |t - phi K θ h y| + |phi K θ h y| := abs_add_le _ _
          _ ≤ R := by rw [hR]; linarith
      have htI : t ∈ Set.Icc (-R) R := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      rw [Set.indicator_of_mem htI, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_pow, abs_of_nonneg (Fd_nn K θ y), abs_of_nonneg (psi_nn ε hε _)]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg t) htR k)
        (mul_le_mul_of_nonneg_left (psi_le ε hε _) (Fd_nn K θ y))
        (mul_nonneg (Fd_nn K θ y) (psi_nn ε hε _)) (pow_nonneg hR0 k)
    · have : psi ε (t - phi K θ h y) = 0 := Set.indicator_of_notMem ht _
      rw [this, mul_zero, mul_zero, norm_zero]; exact hrhs
  · have : Fd K θ y = 0 := Set.indicator_of_notMem hy _
    rw [show t ^ k * (Fd K θ y * psi ε (t - phi K θ h y)) = 0 by rw [this]; ring, norm_zero]
    exact hrhs

theorem mom {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∫ t, t ^ k * dens K θ h ε t = ∫ y, Fd K θ y * ((2 * ε)⁻¹ *
      (((phi K θ h y + ε) ^ (k + 1) - (phi K θ h y - ε) ^ (k + 1)) / (k + 1))) := by
  calc ∫ t, t ^ k * dens K θ h ε t
      = ∫ t, ∫ y, t ^ k * (Fd K θ y * psi ε (t - phi K θ h y)) := by
        congr 1; ext t; unfold dens; rw [← integral_const_mul]
    _ = ∫ y, ∫ t, t ^ k * (Fd K θ y * psi ε (t - phi K θ h y)) :=
        integral_integral_swap (hprod hK θ h ε hε k)
    _ = _ := by
        congr 1; ext y
        rw [← psi_moment ε hε (phi K θ h y) k, ← integral_const_mul]
        congr 1; ext t; ring

theorem lc_dens {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    LogConcaveOn Set.univ (dens K θ h ε) := by
  set f2 : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => Fd K θ z.2 * psi ε (z.1 0 - phi K θ h z.2) with hf2
  have hlc2 : LogConcaveOn Set.univ f2 := by
    have h1 := lc_comp (Fd K θ) (lc_Fd hK θ)
      (fun z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n) => z.2)
      (fun x y a b _ => rfl)
    have h2 := lc_comp (psi ε) (lc_psi ε hε)
      (fun z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n) => z.1 0 - phi K θ h z.2)
      (by
        intro x y a b hab
        simp only [phi, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_sub_left, inner_add_left,
          real_inner_smul_left]
        linear_combination (-⟪meanMap K θ, h⟫) * hab)
    exact lc_mul _ _ h1 h2
  have hcA : Continuous (fun z : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin n) =>
      z.1 0 - phi K θ h z.2) := by
    have := continuous_phi K θ h
    fun_prop
  have hmeas : Measurable f2 :=
    ((measurable_Fd hK θ).comp measurable_snd).mul ((measurable_psi ε).comp hcA.measurable)
  have hfib : ∀ x : EuclideanSpace ℝ (Fin 1), Integrable fun y => f2 (x, y) := by
    intro x
    refine (intF' hK θ (fun _ => (2 * ε)⁻¹) continuous_const).mono'
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hf2, norm_mul, Real.norm_eq_abs, abs_of_nonneg (Fd_nn K θ y),
      abs_of_nonneg (psi_nn ε hε _)]
    exact mul_le_mul_of_nonneg_left (psi_le ε hε _) (Fd_nn K θ y)
  have hmar := prekopa_marginal_log_concave f2 hmeas hlc2 hfib
  have hcomp := lc_comp _ hmar (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t)
    (by
      intro x y a b _
      ext j
      fin_cases j
      simp)
  have e : dens K θ h ε = (fun x => ∫ y, f2 (x, y)) ∘
      (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    funext t
    simp [dens, hf2]
  rw [e]
  exact hcomp

theorem main {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    ∫ x, ⟪x - meanMap K θ, h⟫ ^ 3 ∂(expFamily K θ) ≤
      2 * ((∫ x, ⟪x - meanMap K θ, h⟫ ^ 2 ∂(expFamily K θ)) + ε ^ 2 / 3) ^ ((3 : ℝ) / 2) := by
  have hφ := continuous_phi K θ h
  have hA : ∫ x, ⟪x - meanMap K θ, h⟫ ^ 3 ∂(expFamily K θ) =
      ∫ y, Fd K θ y * phi K θ h y ^ 3 := int_mu hK θ (fun x => ⟪x - meanMap K θ, h⟫ ^ 3)
  have hB : ∫ x, ⟪x - meanMap K θ, h⟫ ^ 2 ∂(expFamily K θ) =
      ∫ y, Fd K θ y * phi K θ h y ^ 2 := int_mu hK θ (fun x => ⟪x - meanMap K θ, h⟫ ^ 2)
  have i1 := intF' hK θ _ hφ
  have i2 := intF' hK θ (fun y => phi K θ h y ^ 2) (hφ.pow 2)
  have i3 := intF' hK θ (fun y => phi K θ h y ^ 3) (hφ.pow 3)
  have i0 := intF' hK θ (fun _ => 1) continuous_const
  have hε' : ε ≠ 0 := hε.ne'
  have m0 : ∫ t, dens K θ h ε t = 1 := by
    have := mom hK θ h ε hε 0
    simp only [pow_zero, one_mul] at this
    rw [this]
    calc _ = ∫ y, Fd K θ y := by
          congr 1; ext y
          push_cast
          field_simp
          ring
      _ = 1 := integral_Fd hK θ
  have m1 : ∫ t, t * dens K θ h ε t = 0 := by
    have := mom hK θ h ε hε 1
    simp only [pow_one] at this
    rw [this]
    calc _ = ∫ y, Fd K θ y * phi K θ h y := by
          congr 1; ext y
          push_cast
          field_simp
          ring
      _ = 0 := centred hK θ h
  have m2 : ∫ t, t ^ 2 * dens K θ h ε t =
      (∫ y, Fd K θ y * phi K θ h y ^ 2) + ε ^ 2 / 3 := by
    rw [mom hK θ h ε hε 2]
    have e : ∀ y, Fd K θ y * ((2 * ε)⁻¹ * (((phi K θ h y + ε) ^ (2 + 1) -
        (phi K θ h y - ε) ^ (2 + 1)) / ((2 : ℕ) + 1 : ℝ))) =
        Fd K θ y * phi K θ h y ^ 2 + ε ^ 2 / 3 * (Fd K θ y * 1) := by
      intro y
      push_cast
      field_simp
      ring
    rw [integral_congr_ae (Eventually.of_forall e), integral_add i2 (i0.const_mul _),
      integral_const_mul]
    have h0 := integral_Fd hK θ
    simp only [mul_one] at h0 ⊢
    rw [h0, mul_one]
  have m3 : ∫ t, t ^ 3 * dens K θ h ε t = ∫ y, Fd K θ y * phi K θ h y ^ 3 := by
    rw [mom hK θ h ε hε 3]
    have e : ∀ y, Fd K θ y * ((2 * ε)⁻¹ * (((phi K θ h y + ε) ^ (3 + 1) -
        (phi K θ h y - ε) ^ (3 + 1)) / ((3 : ℕ) + 1 : ℝ))) =
        Fd K θ y * phi K θ h y ^ 3 + ε ^ 2 * (Fd K θ y * phi K θ h y) := by
      intro y
      push_cast
      field_simp
      ring
    rw [integral_congr_ae (Eventually.of_forall e), integral_add i3 (i1.const_mul _),
      integral_const_mul, centred hK θ h, mul_zero, add_zero]
  have key := EntropicBarrier.Universal.lemma2_third_moment (dens K θ h ε) (lc_dens hK θ h ε hε)
    m0 m1
  rw [m2, m3] at key
  rw [hA, hB]
  exact key

end EBMI

open EntropicBarrier.Universal in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ h : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪x - meanMap K θ, h⟫ ^ 3 ∂(expFamily K θ) ≤
      2 * (∫ x, ⟪x - meanMap K θ, h⟫ ^ 2 ∂(expFamily K θ)) ^ ((3 : ℝ) / 2) := by
  set B := ∫ x, ⟪x - meanMap K θ, h⟫ ^ 2 ∂(expFamily K θ)
  have hcont : Continuous (fun e : ℝ => 2 * (B + e ^ 2 / 3) ^ ((3 : ℝ) / 2)) :=
    continuous_const.mul ((Real.continuous_rpow_const (by norm_num)).comp (by fun_prop))
  have ht : Tendsto (fun e : ℝ => 2 * (B + e ^ 2 / 3) ^ ((3 : ℝ) / 2)) (𝓝[>] 0)
      (𝓝 (2 * B ^ ((3 : ℝ) / 2))) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun e he => EBMI.main hK θ h e he)
