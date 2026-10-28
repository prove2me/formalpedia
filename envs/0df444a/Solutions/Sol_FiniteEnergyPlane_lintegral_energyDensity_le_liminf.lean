-- Prove2me | solution 1 for FiniteEnergyPlane.lintegral_energyDensity_le_liminf
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:28:23.254993+00:00
-- url     : https://prove2.me/submissions/330472dd-f8d7-411d-b5b5-c6e73f9a3aaf

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Lower semicontinuity of the energy integrals under pointwise `C¹` convergence. -/
theorem lintegral_energyDensity_le_liminf_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (W : Set ℂ) (hW : IsOpen W) (v : ℕ → ℂ → V n)
    (w : ℂ → V n) (hv : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (v k) W ∧ ∀ z ∈ W, v k z ≠ 0)
    (hw : ContDiffOn ℝ 1 w W) (hw0 : ∀ z ∈ W, w z ≠ 0)
    (hconv : ∀ z ∈ W, Tendsto (fun k => v k z) atTop (𝓝 (w z)) ∧
      Tendsto (fun k => fderiv ℝ (v k) z) atTop (𝓝 (fderiv ℝ w z)))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ w z) ≤
      liminf (fun k => ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ (v k) z)) atTop := by
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  set O : Set (V n) := {y | y ≠ 0} with hO
  have hOo : IsOpen O := isOpen_ne
  have haCd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (aCoord H) y := fun y hy =>
    (haCs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  have hprd : ∀ y : V n, y ≠ 0 → DifferentiableAt ℝ (proj H) y := fun y hy =>
    (hprojs.differentiableOn (by simp) y hy).differentiableAt (hOo.mem_nhds hy)
  -- the density as a function of the value and the derivative
  set G : V n × (ℂ →L[ℝ] V n) → ℝ := fun p =>
    deriv φ (aCoord H p.1) *
        (((fderiv ℝ (aCoord H) p.1).comp p.2) 1 *
            liouville (proj H p.1) (((fderiv ℝ (proj H) p.1).comp p.2) Complex.I) -
          ((fderiv ℝ (aCoord H) p.1).comp p.2) Complex.I *
            liouville (proj H p.1) (((fderiv ℝ (proj H) p.1).comp p.2) 1)) +
      φ (aCoord H p.1) *
        omega0 (((fderiv ℝ (proj H) p.1).comp p.2) 1)
          (((fderiv ℝ (proj H) p.1).comp p.2) Complex.I) with hG
  have hGeq : ∀ (u : ℂ → V n) (z : ℂ), DifferentiableAt ℝ u z → u z ≠ 0 →
      energyDensity H φ u z = G (u z, fderiv ℝ u z) := by
    intro u z hu hne
    have e1 : fderiv ℝ (fun z => aCoord H (u z)) z =
        (fderiv ℝ (aCoord H) (u z)).comp (fderiv ℝ u z) :=
      ((haCd _ hne).hasFDerivAt.comp z hu.hasFDerivAt).fderiv
    have e2 : fderiv ℝ (fun z => proj H (u z)) z =
        (fderiv ℝ (proj H) (u z)).comp (fderiv ℝ u z) :=
      ((hprd _ hne).hasFDerivAt.comp z hu.hasFDerivAt).fderiv
    simp only [energyDensity, ds, dt, e1, e2]
    rfl
  -- continuity of `G` off `y = 0`
  have hj : ∀ k, Continuous fun u : V n => j0 u k := by
    intro k
    unfold j0
    split_ifs
    · exact (continuous_apply _).neg
    · exact continuous_apply _
  have hωc : Continuous fun p : V n × V n => omega0 p.1 p.2 := by
    unfold omega0 dot
    exact continuous_finset_sum _ fun k _ =>
      ((hj k).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)
  have hcompc : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
      Continuous fun p : (V n →L[ℝ] X) × (ℂ →L[ℝ] V n) => p.1.comp p.2 :=
    fun {X} _ _ => isBoundedBilinearMap_comp.continuous
  have hGc : ∀ p : V n × (ℂ →L[ℝ] V n), p.1 ≠ 0 → ContinuousAt G p := by
    intro p hp
    have hn : O ∈ 𝓝 p.1 := hOo.mem_nhds hp
    have ha : ContinuousAt (fun q : V n × (ℂ →L[ℝ] V n) => aCoord H q.1) p :=
      (haCs.continuousOn.continuousAt hn).comp continuousAt_fst
    have hpr : ContinuousAt (fun q : V n × (ℂ →L[ℝ] V n) => proj H q.1) p :=
      (hprojs.continuousOn.continuousAt hn).comp continuousAt_fst
    have hDA : ContinuousAt (fun q : V n × (ℂ →L[ℝ] V n) => (fderiv ℝ (aCoord H) q.1).comp q.2)
        p :=
      hcompc.continuousAt.comp (((haCs.continuousOn_fderiv_of_isOpen hOo (by simp)).continuousAt
        hn).comp continuousAt_fst |>.prodMk continuousAt_snd)
    have hDP : ContinuousAt (fun q : V n × (ℂ →L[ℝ] V n) => (fderiv ℝ (proj H) q.1).comp q.2)
        p :=
      hcompc.continuousAt.comp (((hprojs.continuousOn_fderiv_of_isOpen hOo (by simp)).continuousAt
        hn).comp continuousAt_fst |>.prodMk continuousAt_snd)
    have ev : ∀ (x : ℂ) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {F : V n × (ℂ →L[ℝ] V n) → (ℂ →L[ℝ] X)}, ContinuousAt F p →
        ContinuousAt (fun q => F q x) p :=
      fun x _ _ _ _ hF => (continuous_eval_const x).continuousAt.comp hF
    have hom : ∀ {f g : V n × (ℂ →L[ℝ] V n) → V n}, ContinuousAt f p → ContinuousAt g p →
        ContinuousAt (fun q => omega0 (f q) (g q)) p :=
      fun hf hg => hωc.continuousAt.comp (hf.prodMk hg)
    have hli : ∀ {f g : V n × (ℂ →L[ℝ] V n) → V n}, ContinuousAt f p → ContinuousAt g p →
        ContinuousAt (fun q => liouville (f q) (g q)) p :=
      fun hf hg => (hom hf hg).div_const 2
    have hdφ : ContinuousAt (fun q : V n × (ℂ →L[ℝ] V n) => deriv φ (aCoord H q.1)) p :=
      (hφ.continuous_deriv le_rfl).continuousAt.comp ha
    have hφa : ContinuousAt (fun q : V n × (ℂ →L[ℝ] V n) => φ (aCoord H q.1)) p :=
      hφ.continuous.continuousAt.comp ha
    exact (hdφ.mul (((ev 1 hDA).mul (hli hpr (ev Complex.I hDP))).sub
      ((ev Complex.I hDA).mul (hli hpr (ev 1 hDP))))).add
      (hφa.mul (hom (ev 1 hDP) (ev Complex.I hDP)))
  -- shift to the good tail
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hv
  set f : ℕ → ℂ → ℝ≥0∞ := fun k z => ENNReal.ofReal (energyDensity H φ (v (k + k₀)) z) with hf
  have hdiffk : ∀ k, ∀ z ∈ W, DifferentiableAt ℝ (v (k + k₀)) z := fun k z hz =>
    (((hk₀ (k + k₀) (by omega)).1.differentiableOn (by simp)) z hz).differentiableAt
      (hW.mem_nhds hz)
  have hmeas : ∀ k, AEMeasurable (f k) (volume.restrict W) := by
    intro k
    obtain ⟨hk1, hk2⟩ := hk₀ (k + k₀) (by omega)
    have hpair : ContinuousOn (fun z => (v (k + k₀) z, fderiv ℝ (v (k + k₀)) z)) W :=
      hk1.continuousOn.prodMk (hk1.continuousOn_fderiv_of_isOpen hW (by simp))
    have hc : ContinuousOn (fun z => energyDensity H φ (v (k + k₀)) z) W := by
      intro z hz
      rw [continuousWithinAt_congr (fun z' hz' => hGeq _ z' (hdiffk k z' hz') (hk2 z' hz'))
        (hGeq _ z (hdiffk k z hz) (hk2 z hz))]
      exact (hGc _ (hk2 z hz)).comp_continuousWithinAt (hpair z hz)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hW.measurableSet)
  have hlim : ∀ z ∈ W, Tendsto (fun k => f k z) atTop
      (𝓝 (ENNReal.ofReal (energyDensity H φ w z))) := by
    intro z hz
    have hwd : DifferentiableAt ℝ w z :=
      ((hw.differentiableOn (by simp)) z hz).differentiableAt (hW.mem_nhds hz)
    rw [hGeq w z hwd (hw0 z hz)]
    refine ENNReal.tendsto_ofReal ?_
    have hsh := tendsto_add_atTop_nat k₀
    have h := (hGc _ (hw0 z hz)).tendsto.comp
      (((hconv z hz).1.comp hsh).prodMk_nhds ((hconv z hz).2.comp hsh))
    refine h.congr fun k => ?_
    exact (hGeq _ z (hdiffk k z hz) ((hk₀ (k + k₀) (by omega)).2 z hz)).symm
  calc ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ w z)
      = ∫⁻ z in W, liminf (fun k => f k z) atTop :=
        setLIntegral_congr_fun hW.measurableSet fun z hz => (hlim z hz).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z in W, f k z) atTop := lintegral_liminf_le' hmeas
    _ = liminf (fun k => ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ (v k) z)) atTop :=
        liminf_nat_add (fun k => ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ (v k) z)) k₀

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (W : Set ℂ) (hW : IsOpen W) (v : ℕ → ℂ → V n)
    (w : ℂ → V n) (hv : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (v k) W ∧ ∀ z ∈ W, v k z ≠ 0)
    (hw : ContDiffOn ℝ 1 w W) (hw0 : ∀ z ∈ W, w z ≠ 0)
    (hconv : ∀ z ∈ W, Tendsto (fun k => v k z) atTop (𝓝 (w z)) ∧
      Tendsto (fun k => fderiv ℝ (v k) z) atTop (𝓝 (fderiv ℝ w z)))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ w z) ≤
      liminf (fun k => ∫⁻ z in W, ENNReal.ofReal (energyDensity H φ (v k) z)) atTop :=
  lintegral_energyDensity_le_liminf_aux H hH J hJ W hW v w hv hw hw0 hconv φ hφ
