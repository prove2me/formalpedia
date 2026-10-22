-- Prove2me | solution 1 for FiniteEnergyPlane.periodicOrbit_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:01:16.414281+00:00
-- url     : https://prove2.me/submissions/14db1114-5eb8-4a89-8465-d79224652fc6

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Setting
import Definitions.Def_HryniewiczCriterion_Basic
open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

namespace G70R

lemma sig_deriv {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun t => ∫ u in (0:ℝ)..t, g u) (g t) t :=
  (hg.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma sig_per {g : ℝ → ℝ} (hg : Continuous g) {T : ℝ} (hp : ∀ t, g (t + T) = g t) (t : ℝ) :
    (∫ u in (0:ℝ)..(t + T), g u) = (∫ u in (0:ℝ)..t, g u) + ∫ u in (0:ℝ)..T, g u := by
  have hd : ∀ x, HasDerivAt (fun t => (∫ u in (0:ℝ)..(t + T), g u) - ∫ u in (0:ℝ)..t, g u) 0 x := by
    intro x
    have h1 := (sig_deriv hg (x + T)).comp x ((hasDerivAt_id x).add_const T)
    have h2 : HasDerivAt _ (0:ℝ) x := (h1.sub (sig_deriv hg x)).congr_deriv (by simp [hp])
    exact h2
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hc
  linarith

lemma sig_lb {g : ℝ → ℝ} (hg : Continuous g) {T : ℝ} (hT : 0 < T) (hp : ∀ t, g (t + T) = g t)
    (hpos : ∀ t, 0 < g t) : ∃ m > 0, ∀ t, m ≤ g t := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_isMinOn
    (Set.nonempty_Icc.2 hT.le) hg.continuousOn
  refine ⟨g x, hpos x, fun t => ?_⟩
  have hP : Function.Periodic g T := hp
  obtain ⟨y, hy, hyt⟩ := hP.exists_mem_Ico₀ hT t
  rw [hyt]; exact hmin ⟨hy.1, hy.2.le⟩

theorem reparam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} {F : E → E} {c : E → ℝ} {T : ℝ} (hT : 0 < T)
    (hy : ∀ t, HasDerivAt y (F (y t)) t) (hper : ∀ t, y (t + T) = y t)
    (hc : Continuous (fun t => c (y t))) (hpos : ∀ t, 0 < c (y t)) :
    ∃ φ : ℝ → ℝ, (∀ s, HasDerivAt (fun s => y (φ s)) ((c (y (φ s)))⁻¹ • F (y (φ s))) s) ∧
      (∀ s, HasDerivAt φ (c (y (φ s)))⁻¹ s) ∧ φ 0 = 0 ∧ Function.Surjective φ ∧
      0 < (∫ u in (0:ℝ)..T, c (y u)) ∧
      ∀ s, φ (s + ∫ u in (0:ℝ)..T, c (y u)) = φ s + T := by
  set g := fun t => c (y t) with hgdef
  have hgp : ∀ t, g (t + T) = g t := fun t => by simp [hgdef, hper]
  set σ := fun t => ∫ u in (0:ℝ)..t, g u with hσ
  have hσd : ∀ t, HasDerivAt σ (g t) t := sig_deriv hc
  have hmono : StrictMono σ := strictMono_of_deriv_pos (fun x => by rw [(hσd x).deriv]; exact hpos x)
  have hcont : Continuous σ := continuous_iff_continuousAt.2 fun x => (hσd x).continuousAt
  obtain ⟨m, hm, hmg⟩ := sig_lb hc hT hgp hpos
  have hd2 : ∀ x, HasDerivAt (fun t => σ t - m * t) (g x - m) x := fun x => by
    convert (hσd x).sub ((hasDerivAt_id' x).const_mul m) using 1 <;> first | rfl | ring | (funext t; rfl)
  have hmon2 : Monotone (fun t => σ t - m * t) := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hd2 x).differentiableAt
    · intro x
      rw [(hd2 x).deriv]; linarith [hmg x]
  have h0 : σ 0 = 0 := by simp [hσ]
  have hup : ∀ t, 0 ≤ t → m * t ≤ σ t := fun t ht => by
    have := hmon2 ht; simp [h0] at this; linarith
  have hdn : ∀ t, t ≤ 0 → σ t ≤ m * t := fun t ht => by
    have := hmon2 ht; simp [h0] at this; linarith
  have hsurj : Function.Surjective σ := by
    apply hcont.surjective
    · refine tendsto_atTop_mono' atTop ?_ ((tendsto_id.const_mul_atTop hm))
      filter_upwards [eventually_ge_atTop 0] with t ht using hup t ht
    · refine tendsto_atBot_mono' atBot ?_ ((tendsto_id.const_mul_atBot hm))
      filter_upwards [eventually_le_atBot 0] with t ht using hdn t ht
  set e := StrictMono.orderIsoOfSurjective σ hmono hsurj
  have he : ∀ t, e t = σ t := fun t => rfl
  have hST : 0 < σ T := by rw [← h0]; exact hmono hT
  refine ⟨e.symm, ?_, ?_, ?_, e.symm.surjective, hST, ?_⟩
  · have hφd : ∀ s, HasDerivAt e.symm (g (e.symm s))⁻¹ s := by
      intro s
      apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
      · exact hσd _
      · exact (hpos _).ne'
      · exact Eventually.of_forall fun z => by rw [← he]; simp
    intro s
    have := (hy (e.symm s)).scomp s (hφd s)
    simpa [Function.comp_def, hgdef] using this
  · intro s
    apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
    · exact hσd _
    · exact (hpos _).ne'
    · exact Eventually.of_forall fun z => by rw [← he]; simp
  · rw [OrderIso.symm_apply_eq, he, h0]
  · intro s
    rw [OrderIso.symm_apply_eq, he]
    show s + σ T = σ (e.symm s + T)
    rw [show σ (e.symm s + T) = σ (e.symm s) + σ T from sig_per hc hgp _, ← he]; simp
    exact (e.apply_symm_apply s).symm

end G70R

namespace G70R

lemma vf (H₀ : HryniewiczCriterion.R4 → ℝ) (x : V 1) :
    hamVF (n := 1) H₀ x = HryniewiczCriterion.hamiltonianVectorField H₀ x := by
  funext k
  fin_cases k <;> simp [hamVF, j0, grad, HryniewiczCriterion.hamiltonianVectorField,
    HryniewiczCriterion.partialDeriv]

lemma fd_sum (H₀ : HryniewiczCriterion.R4 → ℝ) (x : HryniewiczCriterion.R4) :
    fderiv ℝ H₀ x x = ∑ k, x k * fderiv ℝ H₀ x (Pi.single k 1) := by
  have hx : x = ∑ k, x k • (Pi.single k (1:ℝ) : HryniewiczCriterion.R4) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  calc fderiv ℝ H₀ x x = fderiv ℝ H₀ x (∑ k, x k • (Pi.single k (1:ℝ) : HryniewiczCriterion.R4)) := by
        rw [← hx]
    _ = _ := by simp [map_sum, map_smul]

lemma j0e (x : V 1) : j0 x = ![-x 1, x 0, -x 3, x 2] := by
  funext k; fin_cases k <;> simp [j0]

lemma lam (H₀ : HryniewiczCriterion.R4 → ℝ) (x : V 1) :
    liouville (n := 1) x (hamVF H₀ x) = fderiv ℝ H₀ x x / 2 := by
  rw [vf, fd_sum]
  simp only [liouville, omega0, dot, j0e, Fin.sum_univ_four, HryniewiczCriterion.hamiltonianVectorField,
    HryniewiczCriterion.partialDeriv]
  simp [Fin.sum_univ_succ]
  ring

end G70R

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    (IsStrictlyStarShapedLevel H ↔ HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) ∧
      (HryniewiczCriterion.IsStrictlyStarShapedLevel H₀ →
        (∀ P : HryniewiczCriterion.PeriodicOrbit H₀, ∃ Q : ReebOrbit H,
          Set.range Q.x = Set.range (fun τ => toV (P.x τ)) ∧
            Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ)) ∧
        ∀ Q : ReebOrbit H, ∃ P : HryniewiczCriterion.PeriodicOrbit H₀,
          Set.range (fun τ => toV (P.x τ)) = Set.range Q.x ∧
            Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ)) := by
  intro toV H
  refine ⟨Iff.rfl, fun hS => ⟨fun P => ?_, fun Q => ?_⟩⟩
  · have hfd : Continuous (fderiv ℝ H₀) := hS.1.continuous_fderiv (by simp)
    have hy : ∀ t, HasDerivAt (fun t => (P.x t : V 1)) (hamVF (n := 1) H (P.x t)) t := fun t => by
      rw [G70R.vf]; exact P.trajectory.1 t
    have hyc : Continuous (fun t => (P.x t : V 1)) :=
      continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
    have hc : Continuous (fun t => liouville (n := 1) (P.x t) (hamVF H (P.x t))) := by
      simp only [G70R.lam]
      exact ((hfd.comp hyc).clm_apply hyc).div_const 2
    have hpos : ∀ t, 0 < liouville (n := 1) (P.x t) (hamVF H (P.x t)) := fun t => by
      rw [G70R.lam]; have := hS.2.2 _ (P.trajectory.2 t); positivity
    obtain ⟨φ, hφ1, -, -, hsurj, hTpos, hper⟩ :=
      G70R.reparam (c := fun x => liouville (n := 1) x (hamVF H x)) P.T_pos hy P.periodic hc hpos
    refine ⟨{ x := fun s => P.x (φ s), T := _, T_pos := hTpos,
              mem := fun τ => P.trajectory.2 (φ τ),
              hasDerivAt := fun τ => hφ1 τ,
              periodic := fun τ => by rw [hper, P.periodic] }, ?_, ?_⟩
    · show Set.range ((fun t => (P.x t : V 1)) ∘ φ) = _
      rw [Set.range_comp, hsurj.range_eq, Set.image_univ]; rfl
    · show _ = _
      refine intervalIntegral.integral_congr fun τ _ => ?_
      change _ = liouville (n := 1) (P.x τ) (deriv (fun s => (P.x s : V 1)) τ)
      rw [(hy τ).deriv]
  · have hfd : Continuous (fderiv ℝ H₀) := hS.1.continuous_fderiv (by simp)
    have hyc : Continuous Q.x := continuous_iff_continuousAt.2 fun t => (Q.hasDerivAt t).continuousAt
    have hlc : Continuous (fun t => liouville (n := 1) (Q.x t) (hamVF H (Q.x t))) := by
      simp only [G70R.lam]
      exact ((hfd.comp hyc).clm_apply hyc).div_const 2
    have hlpos : ∀ t, 0 < liouville (n := 1) (Q.x t) (hamVF H (Q.x t)) := fun t => by
      rw [G70R.lam]; have := hS.2.2 _ (Q.mem t); positivity
    have hc : Continuous (fun t => (liouville (n := 1) (Q.x t) (hamVF H (Q.x t)))⁻¹) :=
      hlc.inv₀ fun t => (hlpos t).ne'
    obtain ⟨φ, hφ1, hφ2, hφ0, hsurj, hTpos, hper⟩ :=
      G70R.reparam (c := fun x => (liouville (n := 1) x (hamVF H x))⁻¹) Q.T_pos Q.hasDerivAt
        Q.periodic hc (fun t => inv_pos.2 (hlpos t))
    have hz : ∀ s, HasDerivAt (fun s => Q.x (φ s)) (hamVF H (Q.x (φ s))) s := fun s => by
      have := hφ1 s
      simp only [inv_inv, reeb, smul_smul] at this
      rwa [mul_inv_cancel₀ (hlpos _).ne', one_smul] at this
    refine ⟨{ x := fun s => Q.x (φ s), T := _, T_pos := hTpos,
              trajectory := ⟨fun t => by rw [← G70R.vf]; exact hz t, fun t => Q.mem (φ t)⟩,
              periodic := fun τ => by rw [hper, Q.periodic] }, ?_, ?_⟩
    · show Set.range (Q.x ∘ φ) = _
      rw [Set.range_comp, hsurj.range_eq, Set.image_univ]
    · show _ = ∫ τ in (0:ℝ)..(∫ u in (0:ℝ)..Q.T, _), _
      have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ2 t).continuousAt
      rw [intervalIntegral.integral_congr (g := fun τ => liouville (n := 1) (Q.x (φ τ)) (hamVF H (Q.x (φ τ))))
        (fun τ _ => by
          change liouville (n := 1) (Q.x (φ τ)) (deriv (fun s => Q.x (φ s)) τ) = _
          rw [(hz τ).deriv])]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := φ) (f' := fun x => liouville (n := 1) (Q.x (φ x)) (hamVF H (Q.x (φ x))))
        (fun τ _ => by simpa only [inv_inv] using hφ2 τ) ((hlc.comp hφc).intervalIntegrable _ _)]
      have := hper 0
      rw [zero_add, hφ0, zero_add] at this
      rw [this, hφ0, sub_zero]
