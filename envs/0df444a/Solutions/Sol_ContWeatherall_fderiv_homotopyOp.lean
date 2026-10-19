-- Prove2me | solution 1 for ContWeatherall.fderiv_homotopyOp
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T22:08:00.676616+00:00
-- url     : https://prove2.me/submissions/331288ef-008e-4eaa-ace2-72c9d2b3f312

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff Interval

namespace ContWeatherall

/-- Derivative of a parametric interval integral with smooth integrand. -/
theorem fho_hasFDerivAt_param {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : H → ℝ → G} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (a b : ℝ) (x₀ : H) :
    HasFDerivAt (fun x => ∫ t in a..b, f x t)
      (∫ t in a..b, fderiv ℝ (fun y => f y t) x₀) x₀ := by
  set f' : H → ℝ → H →L[ℝ] G := fun x t => fderiv ℝ (fun y => f y t) x with hf'def
  have hf' : ContDiff ℝ ∞ (Function.uncurry f') := by
    have := ContDiff.fderiv (f := fun (p : H × ℝ) (y : H) => f y p.2) (g := fun p => p.1)
      (m := ∞) (n := ∞)
      (hf.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
      contDiff_fst (by simp)
    exact this
  have hdiff : ∀ x t, HasFDerivAt (fun y => f y t) (f' x t) x := by
    intro x t
    have : ContDiff ℝ ∞ (fun y => f y t) :=
      hf.comp (contDiff_id.prodMk contDiff_const)
    exact (this.differentiable (by simp) x).hasFDerivAt
  have hcont : ∀ x, Continuous (f x) := fun x =>
    hf.continuous.comp (continuous_const.prodMk continuous_id)
  have hcont' : ∀ x, Continuous (f' x) := fun x =>
    hf'.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    (hcont' x₀).continuousOn
  have hev : ∀ᶠ x in nhds x₀, ∀ t ∈ Set.uIcc a b, ‖f' x t‖ < C + 1 := by
    refine (isCompact_uIcc (a := a) (b := b)).eventually_forall_of_forall_eventually ?_
    intro t ht
    have hc : Continuous fun z : H × ℝ => ‖f' z.1 z.2‖ := hf'.continuous.norm
    exact hc.continuousAt.eventually_lt continuousAt_const
      (by simpa using (hC t ht).trans_lt (lt_add_one C))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (bound := fun _ => C + 1)
    hev (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
    ((hcont x₀).intervalIntegrable _ _) (hcont' x₀).aestronglyMeasurable ?_
    intervalIntegrable_const ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx => ?_
    exact (hx t (Set.uIoc_subset_uIcc ht)).le
  · exact Filter.Eventually.of_forall fun t x _ => hdiff x t

theorem fho_apply_integral {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] (φ : ℝ → H →L[ℝ] G)
    (hφ : Continuous φ) (a b : ℝ) (h : H) :
    (∫ t in a..b, φ t) h = ∫ t in a..b, φ t h :=
  ((ContinuousLinearMap.apply ℝ G h).intervalIntegral_comp_comm
    (hφ.intervalIntegrable a b)).symm

theorem fho_curryLeft_hasDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {a : ℝ → E [⋀^Fin (k + 1)]→L[ℝ] F}
    {a' : E [⋀^Fin (k + 1)]→L[ℝ] F} {s₀ : ℝ} (ha : HasDerivAt a a' s₀) (y : E) :
    HasDerivAt (fun s => (a s).curryLeft y) (a'.curryLeft y) s₀ := by
  let L : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
    LinearMap.mkContinuous
      { toFun := fun A => A.curryLeft y
        map_add' := fun A B => by simp [curryLeft_add]
        map_smul' := fun c A => by simp [curryLeft_smul] } ‖y‖ (fun A => by
      calc ‖A.curryLeft y‖ ≤ ‖A.curryLeft‖ * ‖y‖ := A.curryLeft.le_opNorm y
        _ = ‖y‖ * ‖A‖ := by rw [norm_curryLeft, mul_comm])
  exact L.hasFDerivAt.comp_hasDerivAt s₀ ha

theorem fho_main {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) (x h : E) :
    fderiv ℝ (homotopyOp w) x h = ∫ t in (0 : ℝ)..1,
      t ^ k • (t • (fderiv ℝ w (t • x) h).curryLeft x + (w (t • x)).curryLeft h) := by
  let C : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) :=
    (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := k)).toContinuousLinearMap
  let f : E → ℝ → E [⋀^Fin k]→L[ℝ] F := fun y t => t ^ k • (C (w (t • y))) y
  have hfeq : homotopyOp w = fun y => ∫ t in (0 : ℝ)..1, f y t := rfl
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    (contDiff_snd.pow k).smul
      ((C.contDiff.comp (hw.comp (contDiff_snd.smul contDiff_fst))).clm_apply contDiff_fst)
  rw [hfeq, (fho_hasFDerivAt_param hf 0 1 x).fderiv]
  have hf' : ContDiff ℝ ∞ (fun t => fderiv ℝ (fun y => f y t) x) := by
    have := ContDiff.fderiv (f := fun (t : ℝ) (y : E) => f y t) (g := fun _ => x)
      (m := ∞) (n := ∞)
      (hf.comp (contDiff_snd.prodMk (contDiff_fst))) contDiff_const (by simp)
    exact this
  rw [fho_apply_integral _ hf'.continuous]
  refine intervalIntegral.integral_congr fun t _ => ?_
  -- directional derivative along `s ↦ x + s • h`
  have hl : HasDerivAt (fun s : ℝ => x + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have hdiff : DifferentiableAt ℝ (fun y => f y t) x :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x
  have h1 : HasDerivAt (fun s : ℝ => f (x + s • h) t) (fderiv ℝ (fun y => f y t) x h) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hw1 : HasDerivAt (fun s : ℝ => w (t • (x + s • h))) (fderiv ℝ w (t • x) (t • h)) 0 := by
    have hl' : HasDerivAt (fun s : ℝ => t • (x + s • h)) (t • h) 0 := hl.const_smul t
    exact ((hw.differentiable (by simp) (t • x)).hasFDerivAt).comp_hasDerivAt_of_eq 0 hl'
      (by simp)
  have hA := fho_curryLeft_hasDerivAt hw1 x
  have hB := (hasDerivAt_id (0 : ℝ)).smul (fho_curryLeft_hasDerivAt hw1 h)
  have h2 : HasDerivAt (fun s : ℝ => f (x + s • h) t)
      (t ^ k • ((fderiv ℝ w (t • x) (t • h)).curryLeft x +
        ((id (0 : ℝ)) • (fderiv ℝ w (t • x) (t • h)).curryLeft h +
          (1 : ℝ) • (w (t • (x + (0 : ℝ) • h))).curryLeft h))) 0 := by
    have := (hA.add hB).const_smul (t ^ k)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [f, map_add, map_smul]
    rfl
  rw [h1.unique h2]
  simp [map_smul, curryLeft_smul]

end ContWeatherall

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) (x h : E) :
    fderiv ℝ (ContWeatherall.homotopyOp w) x h = ∫ t in (0 : ℝ)..1,
      t ^ k • (t • (fderiv ℝ w (t • x) h).curryLeft x + (w (t • x)).curryLeft h) :=
  ContWeatherall.fho_main hw x h
