-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.weak_cauchyRiemann_ae_eq_analytic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:50.852562+00:00
-- url     : https://prove2.me/submissions/2f34c457-615d-4efb-a8e8-d150af460f04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.weak_cauchyRiemann_ae_eq_analytic
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Theorems.Thm_BookProof_WeylCauchyRiemann_exists_analyticOn_ae_eq_ball
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U) (hCR : WeakCauchyRiemannOn f U) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ ∀ᵐ z : ℂ, z ∈ U → f z = g z := by

  classical
  -- a local analytic representative around every point of `U`
  have hloc : ∀ c ∈ U, ∃ (ρ : ℝ) (gc : ℂ → ℂ), 0 < ρ ∧ ball c ρ ⊆ U ∧
      AnalyticOn ℂ gc (ball c ρ) ∧ ∀ᵐ z : ℂ, z ∈ ball c ρ → f z = gc z := by
    intro c hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU c hc
    have hsub : closedBall c (ε / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨gc, hgc, hae⟩ :=
      exists_analyticOn_ae_eq_ball hf hCR (by linarith : (0 : ℝ) < ε / 2) hsub
    exact ⟨ε / 2 / 4, gc, by linarith, (ball_subset_ball (by linarith)).trans hball, hgc, hae⟩
  choose! ρ gc hρ hballU hana hae using hloc
  -- the local representatives agree on overlaps
  have hagree : ∀ c ∈ U, ∀ z ∈ U, EqOn (gc c) (gc z) (ball c (ρ c) ∩ ball z (ρ z)) := by
    intro c hc z hz
    have hopen : IsOpen (ball c (ρ c) ∩ ball z (ρ z)) := isOpen_ball.inter isOpen_ball
    refine MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hopen
      (((hana c hc).continuousOn).mono inter_subset_left)
      (((hana z hz).continuousOn).mono inter_subset_right)
    rw [Filter.EventuallyEq, ae_restrict_iff' hopen.measurableSet]
    filter_upwards [hae c hc, hae z hz] with w h1 h2 hw
    rw [← h1 hw.1, ← h2 hw.2]
  set G : ℂ → ℂ := fun z => gc z z with hGdef
  have hGloc : ∀ c ∈ U, ∀ w ∈ ball c (ρ c), G w = gc c w := by
    intro c hc w hw
    have hwU : w ∈ U := hballU c hc hw
    exact (hagree c hc w hwU ⟨hw, mem_ball_self (hρ w hwU)⟩).symm
  refine ⟨G, ?_, ?_⟩
  · rw [hU.analyticOn_iff_analyticOnNhd]
    intro c hc
    have hEq : EqOn G (gc c) (ball c (ρ c)) := fun w hw => hGloc c hc w hw
    have hAt : AnalyticAt ℂ (gc c) c :=
      ((isOpen_ball.analyticOn_iff_analyticOnNhd).1 (hana c hc)) c (mem_ball_self (hρ c hc))
    exact hAt.congr (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self (hρ c hc)))
      hEq).symm
  · -- a countable subcover makes the exceptional set null
    obtain ⟨T, hTU, hTc, hTeq⟩ :=
      TopologicalSpace.isOpen_biUnion_countable U (fun c => ball c (ρ c))
        (fun c _ => isOpen_ball)
    have hcover : U ⊆ ⋃ c ∈ T, ball c (ρ c) := by
      rw [hTeq]
      intro z hz
      exact mem_biUnion hz (mem_ball_self (hρ z hz))
    rw [ae_iff]
    have hsubset : {z : ℂ | ¬(z ∈ U → f z = G z)} ⊆
        ⋃ c ∈ T, {z : ℂ | ¬(z ∈ ball c (ρ c) → f z = gc c z)} := by
      intro z hz
      simp only [mem_setOf_eq, Classical.not_imp] at hz
      obtain ⟨hzU, hzne⟩ := hz
      obtain ⟨c, hcT, hzc⟩ := mem_iUnion₂.1 (hcover hzU)
      refine mem_iUnion₂.2 ⟨c, hcT, ?_⟩
      simp only [mem_setOf_eq, Classical.not_imp]
      exact ⟨hzc, fun hcon => hzne (by rw [hGloc c (hTU hcT) z hzc]; exact hcon)⟩
    exact measure_mono_null hsubset
      ((measure_biUnion_null_iff hTc).2 fun c hc => ae_iff.1 (hae c (hTU hc)))
