-- Prove2me | solution 1 for ChenBullwhip.Decentralized.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:23:10.653336+00:00
-- url     : https://prove2.me/submissions/e949e319-4db8-4440-9219-caabaf5f050b

import Mathlib
import Definitions.Def_ChenBullwhip_Decentralized_IIDDemand
import Definitions.Def_ChenBullwhip_Decentralized_SingleStage

open MeasureTheory ProbabilityTheory

namespace ChenBullwhipEq6Aux

open ChenBullwhip.Decentralized

/-- forecast error as a function of the error path `x`. -/
noncomputable def ferr (p : ℕ) (x : ℤ → ℝ) (s : ℤ) : ℝ :=
  x s - (∑ j ∈ Finset.Icc 1 p, x (s - j)) / p

/-- sigma-hat as a function of the error path `x`. -/
noncomputable def sh (C : ℝ) (p : ℕ) (x : ℤ → ℝ) (s : ℤ) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 p, (ferr p x (s - i)) ^ 2) / p)

lemma ferr_neg (p : ℕ) (x : ℤ → ℝ) (s : ℤ) : ferr p (-x) s = -ferr p x s := by
  simp only [ferr, Pi.neg_apply, Finset.sum_neg_distrib]
  ring

lemma sh_neg (C : ℝ) (p : ℕ) (x : ℤ → ℝ) (s : ℤ) : sh C p (-x) s = sh C p x s := by
  simp only [sh, ferr_neg, neg_sq]

lemma continuous_ferr (p : ℕ) (s : ℤ) : Continuous (fun x : ℤ → ℝ => ferr p x s) := by
  unfold ferr; fun_prop

lemma continuous_sh (C : ℝ) (p : ℕ) (s : ℤ) : Continuous (fun x : ℤ → ℝ => sh C p x s) := by
  unfold sh
  have := fun i : ℕ => continuous_ferr p (s - i)
  fun_prop

lemma sum_shift (f : ℤ → ℝ) (t : ℤ) (p : ℕ) :
    ∑ i ∈ Finset.Icc 1 p, f (t - i) - ∑ i ∈ Finset.Icc 1 p, f (t - 1 - i)
      = f (t - 1) - f (t - 1 - p) := by
  induction p with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h1 : t - ((n + 1 : ℕ) : ℤ) = t - 1 - n := by push_cast; ring
    rw [h1]
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma forecastError_eq (X : IIDDemand P) {p : ℕ} (hp : 1 ≤ p) (s : ℤ) (ω : Ω) :
    X.forecastError p s ω = ferr p (fun r => X.eps r ω) s := by
  have hp' : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  simp only [IIDDemand.forecastError, IIDDemand.leadTimeForecast, IIDDemand.D, ferr,
    Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : ((p + 1 - 1 : ℕ) : ℝ) = p := by simp
  rw [this]
  field_simp
  ring

lemma sigmaHat_eq (X : IIDDemand P) (C : ℝ) {p : ℕ} (hp : 1 ≤ p) (s : ℤ) (ω : Ω) :
    X.sigmaHat C p s ω = sh C p (fun r => X.eps r ω) s := by
  simp only [IIDDemand.sigmaHat, sh, forecastError_eq X hp]

lemma measurable_path (X : IIDDemand P) : Measurable (fun ω (s : ℤ) => X.eps s ω) :=
  measurable_pi_lambda _ X.measurable_eps

lemma map_neg_eq [IsProbabilityMeasure P] (X : IIDDemand P) :
    P.map (fun ω (s : ℤ) => X.eps s ω) = P.map (fun ω (s : ℤ) => -X.eps s ω) := by
  have h1 := X.indep.map_fun_eq_infinitePi_map₀'
    (fun s => (X.measurable_eps s).aemeasurable)
  have hneg : iIndepFun (fun s ω => -X.eps s ω) P :=
    X.indep.comp (fun _ x => -x) (fun _ => measurable_neg)
  have h2 := hneg.map_fun_eq_infinitePi_map₀'
    (fun s => (X.measurable_eps s).neg.aemeasurable)
  calc P.map (fun ω (s : ℤ) => X.eps s ω)
      = Measure.infinitePi (fun i => P.map (X.eps i)) := h1
    _ = Measure.infinitePi (fun i => P.map (fun ω => -X.eps i ω)) := by
        congr 1
        funext s
        exact (X.symmetric s).map_eq
    _ = P.map (fun ω (s : ℤ) => -X.eps s ω) := h2.symm

lemma integral_odd_eq_zero [IsProbabilityMeasure P] (X : IIDDemand P) (φ : (ℤ → ℝ) → ℝ)
    (hφ : Measurable φ) (hodd : ∀ x, φ (-x) = -φ x) :
    ∫ ω, φ (fun s => X.eps s ω) ∂P = 0 := by
  have hE := measurable_path X
  have hE' : Measurable (fun ω (s : ℤ) => -X.eps s ω) :=
    measurable_pi_lambda _ (fun s => (X.measurable_eps s).neg)
  have h1 : ∫ ω, φ (fun s => X.eps s ω) ∂P = ∫ x, φ x ∂(P.map (fun ω s => X.eps s ω)) :=
    (integral_map hE.aemeasurable hφ.aestronglyMeasurable).symm
  have h2 : ∫ ω, φ (fun s => -X.eps s ω) ∂P = ∫ x, φ x ∂(P.map (fun ω s => -X.eps s ω)) :=
    (integral_map hE'.aemeasurable hφ.aestronglyMeasurable).symm
  have h3 : ∫ ω, φ (fun s => -X.eps s ω) ∂P = - ∫ ω, φ (fun s => X.eps s ω) ∂P := by
    rw [← integral_neg]
    congr 1
    funext ω
    rw [← hodd]
    rfl
  rw [map_neg_eq X] at h1
  linarith

lemma memLp_ferr (X : IIDDemand P) (p : ℕ) (s : ℤ) :
    MemLp (fun ω => ferr p (fun r => X.eps r ω) s) 2 P := by
  have heq : (fun ω => ferr p (fun r => X.eps r ω) s)
      = fun ω => X.eps s ω - (p : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 p, X.eps (s - j) ω := by
    funext ω
    simp only [ferr, div_eq_inv_mul]
  rw [heq]
  refine (X.memLp s).sub ?_
  exact (memLp_finsetSum (Finset.Icc 1 p) (fun (j : ℕ) _ => X.memLp (s - (j : ℤ)))).const_mul _

lemma memLp_sh [IsProbabilityMeasure P] (X : IIDDemand P) (C : ℝ) (p : ℕ) (s : ℤ) :
    MemLp (fun ω => sh C p (fun r => X.eps r ω) s) 2 P := by
  have hm : Measurable (fun ω => sh C p (fun r => X.eps r ω) s) :=
    (continuous_sh C p s).measurable.comp (measurable_path X)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have heq : (fun ω => (sh C p (fun r => X.eps r ω) s) ^ 2)
      = fun ω => C ^ 2 * ((∑ i ∈ Finset.Icc 1 p, (ferr p (fun r => X.eps r ω) (s - i)) ^ 2) / p) := by
    funext ω
    simp only [sh]
    rw [mul_pow, Real.sq_sqrt]
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · exact Nat.cast_nonneg p
  rw [heq]
  refine Integrable.const_mul ?_ _
  refine Integrable.div_const ?_ _
  exact integrable_finsetSum _ (fun i _ => (memLp_ferr X p (s - i)).integrable_sq)

end ChenBullwhipEq6Aux

open MeasureTheory ProbabilityTheory ChenBullwhip.Decentralized in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : IIDDemand P) (p L : ℕ) (hp : 1 ≤ p) (C z : ℝ) (t : ℤ) :
    variance (X.order C z L p t) P / variance (X.D t) P
      ≥ 1 + 2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
  have hp' : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  set a : ℝ := 1 + (L : ℝ) / p with ha
  set b : ℝ := (L : ℝ) / p with hb
  let u : (ℤ → ℝ) → ℝ := fun x => a * x (t - 1) + (-b) * x (t - 1 - p)
  let v : (ℤ → ℝ) → ℝ := fun x => z * (ChenBullwhipEq6Aux.sh C p x t - ChenBullwhipEq6Aux.sh C p x (t - 1))
  have hu : Continuous u := by fun_prop
  have hv : Continuous v := by
    have h1 := ChenBullwhipEq6Aux.continuous_sh C p t
    have h2 := ChenBullwhipEq6Aux.continuous_sh C p (t - 1)
    fun_prop
  have hE := ChenBullwhipEq6Aux.measurable_path X
  let U : Ω → ℝ := fun ω => u (fun r => X.eps r ω)
  let V : Ω → ℝ := fun ω => v (fun r => X.eps r ω)
  have hUm : Measurable U := hu.measurable.comp hE
  have hVm : Measurable V := hv.measurable.comp hE
  -- decomposition of the order
  have horder : X.order C z L p t = fun ω => X.mu + (U ω + V ω) := by
    funext ω
    simp only [IIDDemand.order, IIDDemand.orderUpTo, IIDDemand.leadTimeForecast,
      ChenBullwhipEq6Aux.sigmaHat_eq X C hp, U, V, u, v]
    have hs := ChenBullwhipEq6Aux.sum_shift (fun r => X.D r ω) t p
    have hs2 : ∑ i ∈ Finset.Icc 1 p, X.D (t - 1 - i) ω
        = ∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω - (X.D (t - 1) ω - X.D (t - 1 - p) ω) := by
      linarith
    rw [hs2]
    simp only [IIDDemand.D, ha, hb]
    field_simp
    ring
  -- memLp
  have hUL : MemLp U 2 P := by
    have h1 := (X.memLp (t - 1)).const_mul a
    have h2 := (X.memLp (t - 1 - p)).const_mul (-b)
    exact h1.add h2
  have hVL : MemLp V 2 P := by
    have h1 := ChenBullwhipEq6Aux.memLp_sh X C p t
    have h2 := ChenBullwhipEq6Aux.memLp_sh X C p (t - 1)
    exact (h1.sub h2).const_mul z
  -- covariance vanishes
  have hU0 : ∫ ω, U ω ∂P = 0 := by
    apply ChenBullwhipEq6Aux.integral_odd_eq_zero X u hu.measurable
    intro x
    simp only [u, Pi.neg_apply]
    ring
  have hcov : covariance U V P = 0 := by
    unfold covariance
    rw [hU0]
    set c := ∫ ω, V ω ∂P
    have := ChenBullwhipEq6Aux.integral_odd_eq_zero X (fun x => (u x - 0) * (v x - c))
      ((hu.measurable.sub measurable_const).mul (hv.measurable.sub measurable_const))
      (by
        intro x
        simp only [u, v, Pi.neg_apply, ChenBullwhipEq6Aux.sh_neg]
        ring)
    exact this
  -- variance of U
  have hVarU : variance U P = (a ^ 2 + b ^ 2) * X.sigma ^ 2 := by
    have hne : t - 1 ≠ t - 1 - (p : ℤ) := by omega
    have hind : IndepFun (fun ω => a * X.eps (t - 1) ω) (fun ω => (-b) * X.eps (t - 1 - p) ω) P :=
      (X.indep.indepFun hne).comp (measurable_const.mul measurable_id)
        (measurable_const.mul measurable_id)
    have := hind.variance_add ((X.memLp (t - 1)).const_mul a) ((X.memLp (t - 1 - p)).const_mul (-b))
    have hUeq : U = (fun ω => a * X.eps (t - 1) ω) + (fun ω => (-b) * X.eps (t - 1 - p) ω) := by
      funext ω; rfl
    rw [hUeq, this, variance_const_mul, variance_const_mul, X.variance_eq, X.variance_eq]
    ring
  have hVarD : variance (X.D t) P = X.sigma ^ 2 := by
    have : X.D t = fun ω => X.mu + X.eps t ω := rfl
    rw [this, variance_const_add (X.measurable_eps t).aestronglyMeasurable, X.variance_eq]
  have hVarQ : variance (X.order C z L p t) P ≥ variance U P := by
    rw [horder, show (fun ω => X.mu + (U ω + V ω)) = fun ω => X.mu + (U + V) ω from rfl,
      variance_const_add (hUm.add hVm).aestronglyMeasurable, variance_add hUL hVL, hcov]
    have := variance_nonneg V P
    linarith
  have hs2 : 0 < X.sigma ^ 2 := by have := X.sigma_pos; positivity
  rw [hVarD, ge_iff_le, le_div_iff₀ hs2]
  have hkey : 1 + 2 * (L : ℝ) / p + 2 * (L : ℝ) ^ 2 / (p : ℝ) ^ 2 = a ^ 2 + b ^ 2 := by
    rw [ha, hb]
    field_simp
    ring
  rw [hkey, ← hVarU]
  linarith
