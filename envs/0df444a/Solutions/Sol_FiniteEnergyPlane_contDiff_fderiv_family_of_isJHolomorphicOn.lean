-- Prove2me | solution 1 for FiniteEnergyPlane.contDiff_fderiv_family_of_isJHolomorphicOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-08T23:03:46.485555+00:00
-- url     : https://prove2.me/submissions/a2d7d6f3-8b64-48d9-a44d-079095025aab

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_isAlmostComplexOn_tangent
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology JHolomorphic
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem contDiff_fderiv_family_of_isJHolomorphicOn_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (l : ℕ) (hl : 2 ≤ l) (r : ℝ) (g : ℂ × ℝ → V n)
    (hg : ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hmem : ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
      JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t))) :
    ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) := by
  intro t ht
  set Ω : Set (ℂ × ℝ) := Set.univ ×ˢ Set.Ioo (-r) r with hΩ_def
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hmemΩ : ∀ z : ℂ, ∀ s ∈ Set.Ioo (-r) r, ((z, s) : ℂ × ℝ) ∈ Ω :=
    fun z s hs => ⟨Set.mem_univ z, hs⟩
  have hJac := (jtilde_isAlmostComplexOn H hH J hJ).1
  set Jt := Jtilde H J with hJt_def
  set D := fderiv ℝ g with hD_def
  have hg2 : ContDiffOn ℝ 2 g Ω := hg.of_le (by exact_mod_cast hl)
  have hDg : ContDiffOn ℝ 1 D Ω := hg2.fderiv_of_isOpen hΩ (by norm_num)
  -- the inclusion `z ↦ (z, s)`
  have hι : ∀ (s : ℝ) (z : ℂ), HasFDerivAt (fun z : ℂ => ((z, s) : ℂ × ℝ))
      ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℝ)) z :=
    fun s z => (hasFDerivAt_id z).prodMk (hasFDerivAt_const s z)
  -- derivative of a member of the family
  have hchain : ∀ z : ℂ, ∀ s ∈ Set.Ioo (-r) r, ∀ e : ℂ,
      fderiv ℝ (fun w => g (w, s)) z e = D (z, s) (e, 0) := by
    intro z s hs e
    have hdq : DifferentiableAt ℝ g (z, s) :=
      (hg2.contDiffAt (hΩ.mem_nhds (hmemΩ z s hs))).differentiableAt (by simp)
    have h1 : HasFDerivAt (fun w => g (w, s))
        ((D (z, s)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℝ))) z :=
      hdq.hasFDerivAt.comp z (hι s z)
    rw [h1.fderiv]
    simp
  obtain ⟨hsm, hne, hhol⟩ := hmem t ht
  set u : ℂ → V n := fun z => g (z, t) with hu_def
  set ζ : ℂ → V n := fun z => D (z, t) (0, 1) with hζ_def
  -- regularity of `ζ`
  have hζc : ContDiff ℝ 1 ζ := by
    rw [← contDiffOn_univ]
    have hc : ContDiffOn ℝ 1 (fun z : ℂ => ((z, t) : ℂ × ℝ)) Set.univ :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    exact (hDg.comp hc (fun z _ => hmemΩ z t ht)).clm_apply contDiffOn_const
  -- the lift
  set w : ℂ → V n × V n := fun z => (u z, ζ z) with hw_def
  set JT : V n × V n → V n × V n →L[ℝ] V n × V n :=
    fun x : V n × V n => ((Jt x.1).comp (ContinuousLinearMap.fst ℝ (V n) (V n))).prod
        ((Jt x.1).comp (ContinuousLinearMap.snd ℝ (V n) (V n)) +
          (fderiv ℝ Jt x.1 x.2).comp (ContinuousLinearMap.fst ℝ (V n) (V n))) with hJT_def
  have hJT : IsAlmostComplexOn JT ({y : V n | y ≠ 0} ×ˢ Set.univ) :=
    isAlmostComplexOn_tangent Jt {y : V n | y ≠ 0} hJac
  have hwc : ContDiff ℝ 1 w := (hsm.of_le (by simp)).prodMk hζc
  have hwhol : IsJHolomorphicOn JT Set.univ w := by
    intro z _
    have hp : ((z, t) : ℂ × ℝ) ∈ Ω := hmemΩ z t ht
    have hpN : Ω ∈ 𝓝 ((z, t) : ℂ × ℝ) := hΩ.mem_nhds hp
    have hcz : ContDiffAt ℝ 2 g (z, t) := hg2.contDiffAt hpN
    have hdg : DifferentiableAt ℝ g (z, t) := hcz.differentiableAt (by simp)
    have hd2 : DifferentiableAt ℝ D (z, t) := (hDg.contDiffAt hpN).differentiableAt (by simp)
    have hDD := hd2.hasFDerivAt
    have hJd : DifferentiableAt ℝ Jt (g (z, t)) :=
      (hJac.2.1.contDiffAt (hJac.1.mem_nhds (hne z))).differentiableAt (by simp)
    have hu1 : HasFDerivAt u ((D (z, t)).comp
        ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℝ))) z :=
      hdg.hasFDerivAt.comp z (hι t z)
    have hζ1 : HasFDerivAt ζ (((fderiv ℝ D (z, t)).comp
        ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℝ))).flip ((0 : ℂ), (1 : ℝ))) z := by
      have := (hDD.comp z (hι t z)).clm_apply (hasFDerivAt_const (((0 : ℂ), (1 : ℝ))) z)
      simpa using this
    have hv := hu1.prodMk hζ1
    refine ⟨hv.differentiableAt, ?_⟩
    -- differentiate the Cauchy–Riemann equation of the family in the parameter
    have hF := (hDD.clm_apply (hasFDerivAt_const (((1 : ℂ), (0 : ℝ))) (z, t))).add
      ((hJd.hasFDerivAt.comp (z, t) hdg.hasFDerivAt).clm_apply
        (hDD.clm_apply (hasFDerivAt_const ((Complex.I, (0 : ℝ))) (z, t))))
    have hev : (fun q : ℂ × ℝ => D q ((1 : ℂ), (0 : ℝ)) +
        (Jt ∘ g) q (D q (Complex.I, (0 : ℝ)))) =ᶠ[𝓝 (z, t)] fun _ => (0 : V n) := by
      filter_upwards [hpN] with q hq
      obtain ⟨-, hq2⟩ := hq
      have hh := ((hmem q.2 hq2).2.2 q.1 (Set.mem_univ _)).2
      unfold dbarJ at hh
      rw [hchain q.1 q.2 hq2, hchain q.1 q.2 hq2] at hh
      simpa using hh
    have h0 := hF.unique ((hasFDerivAt_const (0 : V n) (z, t)).congr_of_eventuallyEq hev)
    have h0e := congrArg (fun L => L (((0 : ℂ), (1 : ℝ)))) h0
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
      add_zero] at h0e
    -- symmetry of the second derivative
    have hsymm : IsSymmSndFDerivAt ℝ g (z, t) :=
      hcz.isSymmSndFDerivAt (by
        rw [minSmoothness_of_isRCLikeNormedField])
    have hs1 := hsymm ((1 : ℂ), (0 : ℝ)) ((0 : ℂ), (1 : ℝ))
    have hsI := hsymm (Complex.I, (0 : ℝ)) ((0 : ℂ), (1 : ℝ))
    unfold dbarJ
    rw [hv.fderiv]
    simp only [hJT_def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.mk_add_mk, Prod.mk_eq_zero,
      ContinuousLinearMap.coe_id', id, ContinuousLinearMap.prod_apply]
    refine ⟨?_, ?_⟩
    · have hh := (hhol z (Set.mem_univ _)).2
      unfold dbarJ at hh
      rw [hchain z t ht, hchain z t ht] at hh
      simpa using hh
    · rw [hs1, hsI]
      rw [← h0e]
  -- weak formulation and Theorem 2.22 (1)
  have hw1 : ContDiffOn ℝ 1 w Set.univ := hwc.contDiffOn
  have hsmw : ContDiffOn ℝ ∞ w Set.univ := by
    refine contDiffOn_of_isWeakJHolomorphicOn 3 (by norm_num) JT _ hJT Set.univ isOpen_univ w ?_
    have hcf : ContinuousOn (fderiv ℝ w) Set.univ :=
      hw1.continuousOn_fderiv_of_isOpen isOpen_univ le_rfl
    refine ⟨hw1.continuousOn, fun z _ => ⟨hne z, Set.mem_univ _⟩, fun z => fderiv ℝ w z 1,
      fun z => fderiv ℝ w z Complex.I, HasWeakPartialsOn.of_contDiffOn isOpen_univ hw1,
      ?_, ?_⟩
    · intro K hK hKc
      exact ⟨memLp_of_continuousOn_compact hKc (hw1.continuousOn.mono hK),
        memLp_of_continuousOn_compact hKc ((hcf.clm_apply continuousOn_const).mono hK),
        memLp_of_continuousOn_compact hKc ((hcf.clm_apply continuousOn_const).mono hK)⟩
    · exact ae_restrict_of_forall_mem MeasurableSet.univ fun z hz => (hwhol z hz).2
  exact contDiff_snd.comp (contDiffOn_univ.1 hsmw)

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (l : ℕ) (hl : 2 ≤ l) (r : ℝ) (g : ℂ × ℝ → V n)
    (hg : ContDiffOn ℝ l g (Set.univ ×ˢ Set.Ioo (-r) r))
    (hmem : ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => g (z, t)) ∧ (∀ z, g (z, t) ≠ 0) ∧
      JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ (fun z => g (z, t))) :
    ∀ t ∈ Set.Ioo (-r) r, ContDiff ℝ ∞ (fun z => fderiv ℝ g (z, t) (0, 1)) :=
  contDiff_fderiv_family_of_isJHolomorphicOn_aux H hH J hJ l hl r g hg hmem
