-- Prove2me | solution 1 for BirkhoffGlobalSection.regularization_model_transports_closed_orbit
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T23:09:02.98322+00:00
-- url     : https://prove2.me/submissions/b6ede5e0-cfad-4fc5-8a6f-b9deaef6562e

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

open BirkhoffGlobalSection
open scoped ContDiff Topology

set_option autoImplicit false

/-- The Levi-Civita Hamiltonian is `C²` away from the second collision. -/
private lemma lc_contDiffAt (μ c : ℝ) {s : Phase} (hs : 0 < secondCollisionDistanceSq s) :
    ContDiffAt ℝ 2 (leviCivitaHamiltonian μ c) s := by
  have h1 : ContDiffAt ℝ 2 (fun s : Phase => wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2
      + 2 * zNormSq s * (s 0 * s 3 - s 1 * s 2) - μ * (s 0 * s 3 + s 1 * s 2)) s := by
    unfold wNormSq zNormSq; fun_prop
  have h2 : ContDiffAt ℝ 2 (fun s : Phase => μ * zNormSq s) s := by
    unfold zNormSq; fun_prop
  have h3 : ContDiffAt ℝ 2 (fun s : Phase => Real.sqrt (secondCollisionDistanceSq s)) s :=
    ContDiffAt.sqrt (by unfold secondCollisionDistanceSq; fun_prop) hs.ne'
  exact h1.sub (h2.div h3 (Real.sqrt_pos.mpr hs).ne')

/-- The Hamiltonian vector field of a `C²` function is `C¹`. -/
private lemma hvf_contDiffAt {F : Phase → ℝ} {s : Phase} (hF : ContDiffAt ℝ 2 F s) :
    ContDiffAt ℝ 1 (hamiltonianVectorField F) s := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) s := hF.fderiv_right (by norm_num)
  have hp : ∀ i : Fin 4, ContDiffAt ℝ 1 (fun s => partialDerivative F s i) s :=
    fun i => hd.clm_apply contDiffAt_const
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · simpa [hamiltonianVectorField] using hp 2
  · simpa [hamiltonianVectorField] using hp 3
  · simpa [hamiltonianVectorField] using (hp 0).neg
  · simpa [hamiltonianVectorField] using (hp 1).neg

/-- A solution of a locally Lipschitz autonomous equation that returns to its
initial point at time `T` is `T`-periodic. -/
private lemma periodic_of_closed {v : Phase → Phase} {x : ℝ → Phase} {T : ℝ}
    (hv : ∀ t, ∃ K, ∃ s ∈ 𝓝 (x t), LipschitzOnWith K v s)
    (hx : ∀ t, HasDerivAt x (v (x t)) t) (hT : x T = x 0) :
    ∀ t, x (t + T) = x t := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hxTc : Continuous fun t => x (t + T) := hxc.comp (continuous_add_const T)
  set A : Set ℝ := {t | x (t + T) = x t} with hA
  have hclosed : IsClosed A := isClosed_eq hxTc hxc
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have ht₀' : x (t₀ + T) = x t₀ := ht₀
    obtain ⟨K, s, hs, hL⟩ := hv t₀
    have hs' : s ∈ 𝓝 (x (t₀ + T)) := by rw [ht₀']; exact hs
    have hf : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => x (t + T)) (v (x (t + T))) t ∧
        x (t + T) ∈ s := by
      filter_upwards [hxTc.continuousAt.preimage_mem_nhds hs'] with t ht
      exact ⟨HasDerivAt.comp_add_const t T (hx (t + T)), ht⟩
    have hg : ∀ᶠ t in 𝓝 t₀, HasDerivAt x (v (x t)) t ∧ x t ∈ s := by
      filter_upwards [hxc.continuousAt.preimage_mem_nhds hs] with t ht
      exact ⟨hx t, ht⟩
    have heq := ODE_solution_unique_of_eventually (v := fun _ => v) (s := fun _ => s) (K := K)
      (Filter.Eventually.of_forall fun _ => hL) hf hg ht₀'
    filter_upwards [heq] with t ht
    exact ht
  have h0 : (0 : ℝ) ∈ A := by
    show x (0 + T) = x 0
    rw [zero_add, hT]
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0⟩
  intro t
  have ht : t ∈ A := by rw [huniv]; trivial
  exact ht

theorem solution
    (μ c : ℝ) (M : RegularizationModel μ c) (S : Set Phase)
    (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c ∩ M.toModel ⁻¹' S) x T) :
    ∃ (y : ℝ → Phase) (T' : ℝ) (σ : ℝ → ℝ),
      IsPeriodicHamiltonianSolutionIn M.modelHamiltonian S y T' ∧
        StrictMono σ ∧ σ 0 = 0 ∧ σ T = T' ∧
        ∀ t : ℝ, y (σ t) = M.toModel (x t) := by
  obtain ⟨hT0, hmem, hder, hclose⟩ := hx
  have hcomp : ∀ t, x t ∈ leftEnergyComponent μ c := fun t => (hmem t).1
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  -- the orbit is periodic
  have hper : ∀ t, x (t + T) = x t := by
    refine periodic_of_closed (fun t => ?_) hder hclose
    have hreg : x t ∈ regularEnergyLocus μ c := connectedComponentIn_subset _ _ (hcomp t)
    exact (hvf_contDiffAt (lc_contDiffAt μ c hreg.2)).exists_lipschitzOnWith
  -- the regularization clock
  set f : ℝ → ℝ := fun t => M.timeScale (x t) with hf
  have hfc : Continuous f :=
    M.timeScale_continuous.comp_continuous hxc fun t => M.contains_component (hcomp t)
  have hfpos : ∀ t, 0 < f t := fun t => M.timeScale_pos _ (hcomp t)
  have hfper : Function.Periodic f T := fun t => by simp only [hf, hper t]
  obtain ⟨m, hm, hmle⟩ : ∃ m, 0 < m ∧ ∀ t, m ≤ f t := by
    obtain ⟨m, ⟨t₀, ht₀⟩, hmin⟩ :=
      (hfper.compact_of_continuous hT0.ne' hfc).exists_isLeast (Set.range_nonempty f)
    exact ⟨m, ht₀ ▸ hfpos t₀, fun t => hmin ⟨t, rfl⟩⟩
  set σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, f s with hσ
  have hσd : ∀ t, HasDerivAt σ (f t) t := fun t => (hfc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hσ0 : σ 0 = 0 := by simp [hσ]
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσd t).continuousAt
  have hσmono : StrictMono σ :=
    strictMono_of_deriv_pos fun t => by rw [(hσd t).deriv]; exact hfpos t
  -- linear growth of the clock
  have hgd : ∀ t, HasDerivAt (fun t => σ t - m * t) (f t - m) t := fun t => by
    have h := (hσd t).sub ((hasDerivAt_id' t).const_mul m)
    rw [mul_one] at h
    exact h
  have hgmono : Monotone fun t => σ t - m * t := by
    apply monotone_of_deriv_nonneg
    · intro t; exact (hgd t).differentiableAt
    · intro t; rw [(hgd t).deriv]; linarith [hmle t]
  have hsurj : Function.Surjective σ := by
    intro v
    rcases le_or_gt 0 v with hv | hv
    · have hvm : (0 : ℝ) ≤ v / m := div_nonneg hv hm.le
      have hup : v ≤ σ (v / m) := by
        have := hgmono hvm
        simp only at this
        rw [mul_div_cancel₀ v hm.ne', hσ0, mul_zero, sub_zero] at this
        linarith
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc hvm hσc.continuousOn
        ⟨by rw [hσ0]; exact hv, hup⟩
      exact ⟨t, ht⟩
    · have hvm : v / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.le hm.le
      have hlo : σ (v / m) ≤ v := by
        have := hgmono hvm
        simp only at this
        rw [mul_div_cancel₀ v hm.ne', hσ0, mul_zero, sub_zero] at this
        linarith
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc hvm hσc.continuousOn
        ⟨hlo, by rw [hσ0]; exact hv.le⟩
      exact ⟨t, ht⟩
  -- the inverse clock
  set e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective σ hσmono hsurj with he
  have heσ : ∀ t, e.symm (σ t) = t := fun t =>
    StrictMono.orderIsoOfSurjective_symm_apply_self σ hσmono hsurj t
  have hσe : ∀ τ, σ (e.symm τ) = τ := fun τ =>
    StrictMono.orderIsoOfSurjective_self_symm_apply σ hσmono hsurj τ
  -- the transported curve and its derivative
  have hTx : ∀ t, HasDerivAt (fun t => M.toModel (x t))
      (f t • hamiltonianVectorField M.modelHamiltonian (M.toModel (x t))) t := by
    intro t
    have hsrc : x t ∈ M.source := M.contains_component (hcomp t)
    have hdiff : DifferentiableAt ℝ M.toModel (x t) :=
      (M.toModel_smooth.contDiffAt (M.source_open.mem_nhds hsrc)).differentiableAt (by simp)
    have h := hdiff.hasFDerivAt.comp_hasDerivAt t (hder t)
    rw [M.vectorField _ (hcomp t)] at h
    exact h
  have hy : ∀ τ, HasDerivAt (fun τ => M.toModel (x (e.symm τ)))
      (hamiltonianVectorField M.modelHamiltonian (M.toModel (x (e.symm τ)))) τ := by
    intro τ
    have hinv : HasDerivAt e.symm (f (e.symm τ))⁻¹ τ :=
      HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
        (hσd (e.symm τ)) (hfpos _).ne'
        (Filter.Eventually.of_forall hσe)
    have h := (hTx (e.symm τ)).scomp τ hinv
    rw [smul_smul, inv_mul_cancel₀ (hfpos _).ne', one_smul] at h
    exact h
  have he0 : e.symm 0 = 0 := by simpa [hσ0] using heσ 0
  refine ⟨fun τ => M.toModel (x (e.symm τ)), σ T, σ, ⟨?_, ?_, hy, ?_⟩, hσmono, hσ0, rfl, ?_⟩
  · have := hσmono hT0
    rwa [hσ0] at this
  · intro τ
    exact (hmem _).2
  · show M.toModel (x (e.symm (σ T))) = M.toModel (x (e.symm 0))
    rw [heσ, he0, hclose]
  · intro t
    show M.toModel (x (e.symm (σ t))) = M.toModel (x t)
    rw [heσ]
