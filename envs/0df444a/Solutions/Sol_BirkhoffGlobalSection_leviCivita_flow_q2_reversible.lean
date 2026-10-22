-- Prove2me | solution 1 for BirkhoffGlobalSection.leviCivita_flow_q2_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T23:47:05.241477+00:00
-- url     : https://prove2.me/submissions/6fc0ab8d-f7dc-4e38-adb3-0ef3db49d100

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_antipodal_symmetry
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

open BirkhoffGlobalSection
open scoped ContDiff

/-- The Hamiltonian vector field is `C¹` wherever the Hamiltonian is smooth. -/
lemma hvf_contDiffAt (F : Phase → ℝ) (s : Phase) (h : ContDiffAt ℝ ∞ F s) :
    ContDiffAt ℝ 1 (hamiltonianVectorField F) s := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) s := h.fderiv_right (by norm_cast)
  have hp : ∀ i : Fin 4, ContDiffAt ℝ 1 (fun x => partialDerivative F x i) s := fun i =>
    hd.clm_apply contDiffAt_const
  apply contDiffAt_pi'
  intro i
  fin_cases i
  · simpa [hamiltonianVectorField] using hp 2
  · simpa [hamiltonianVectorField] using hp 3
  · simpa [hamiltonianVectorField] using (hp 0).neg
  · simpa [hamiltonianVectorField] using (hp 1).neg

/-- Uniqueness of integral curves inside the compact component. -/
lemma component_curves_unique (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) (f g : ℝ → Phase)
    (hf : ∀ t, f t ∈ leftEnergyComponent μ c ∧
      HasDerivAt f (hamiltonianVectorField (leviCivitaHamiltonian μ c) (f t)) t)
    (hg : ∀ t, g t ∈ leftEnergyComponent μ c ∧
      HasDerivAt g (hamiltonianVectorField (leviCivitaHamiltonian μ c) (g t)) t)
    (h0 : f 0 = g 0) : f = g := by
  obtain ⟨hcpt, hsmooth, -, -, -⟩ := left_energy_component_geometry μ c hμ0 hμ1 hc
  have hloc : LocallyLipschitzOn (leftEnergyComponent μ c)
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)) := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := (hvf_contDiffAt _ x (hsmooth x hx).1).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hcpt
  exact ODE_solution_unique_univ (v := fun _ => hamiltonianVectorField (leviCivitaHamiltonian μ c))
    (s := fun _ => leftEnergyComponent μ c) (t₀ := 0) (fun _ => hK)
    (fun t => ⟨(hf t).2, (hf t).1⟩) (fun t => ⟨(hg t).2, (hg t).1⟩) h0

/-- Every flow line is an integral curve at every time. -/
lemma flow_line_hasDerivAt (μ c : ℝ) (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((φ u x : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)
        ((φ t x : LeftEnergyState μ c) : Phase)) t := by
  have h0 : HasDerivAt (fun u : ℝ => ((φ u (φ t x) : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c)
        ((φ t x : LeftEnergyState μ c) : Phase)) (t - t) := by
    rw [sub_self]; exact hφ (φ t x)
  have h := HasDerivAt.comp_sub_const t t h0
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← Flow.map_add]; congr 1; ring

/-- Precomposition with a linear symmetry of the Hamiltonian. -/
lemma fderiv_symm_apply (F : Phase → ℝ) (L : Phase →L[ℝ] Phase) (hL : ∀ s, F (L s) = F s)
    (s : Phase) (hd : DifferentiableAt ℝ F (L s)) (v : Phase) :
    fderiv ℝ F s v = fderiv ℝ F (L s) (L v) := by
  have e : F = F ∘ L := by funext x; simp [hL]
  have := fderiv_comp s hd L.differentiableAt
  rw [ContinuousLinearMap.fderiv] at this
  conv_lhs => rw [e]
  rw [this]; rfl

/-- The reflection as a continuous linear map. -/
noncomputable def reflCLM : Phase →L[ℝ] Phase :=
  LinearMap.toContinuousLinearMap
    { toFun := jacobiQ₂Reflection
      map_add' := by
        intro x y; funext i; fin_cases i <;> simp [jacobiQ₂Reflection] <;> ring
      map_smul' := by
        intro a x; funext i; fin_cases i <;> simp [jacobiQ₂Reflection] }

lemma reflCLM_apply (s : Phase) : reflCLM s = jacobiQ₂Reflection s := rfl

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∀ t : ℝ, ∀ s₁ s₂ : LeftEnergyState μ c,
      (s₂ : Phase) = jacobiQ₂Reflection (s₁ : Phase) →
        ((φ (-t) s₂ : LeftEnergyState μ c) : Phase) =
          jacobiQ₂Reflection ((φ t s₁ : LeftEnergyState μ c) : Phase) := by
  obtain ⟨-, hinv, -⟩ := antipodal_symmetry μ c hμ0 hμ1 hc
  obtain ⟨-, hsmooth, -, -, -⟩ := left_energy_component_geometry μ c hμ0 hμ1 hc
  set K := leviCivitaHamiltonian μ c
  have hK : ∀ s, K (reflCLM s) = K s := by
    intro s
    simp only [reflCLM_apply, K, leviCivitaHamiltonian, zNormSq, wNormSq,
      secondCollisionDistanceSq, jacobiQ₂Reflection]
    simp
  have hD : ∀ s, secondCollisionDistanceSq (jacobiQ₂Reflection s) = secondCollisionDistanceSq s := by
    intro s; simp [secondCollisionDistanceSq, jacobiQ₂Reflection]
  have hρρ : ∀ s, jacobiQ₂Reflection (jacobiQ₂Reflection s) = s := by
    intro s; funext i; fin_cases i <;> simp [jacobiQ₂Reflection]
  -- the reflection preserves the selected component
  intro t s₁ s₂ hs
  have hρcomp : ∀ s ∈ leftEnergyComponent μ c, jacobiQ₂Reflection s ∈ leftEnergyComponent μ c := by
    have hpE := connectedComponentIn_nonempty_iff.1 ⟨_, s₁.2⟩
    have hp : leftCollisionPoint μ ∈ leftEnergyComponent μ c := mem_connectedComponentIn hpE
    have hρp : jacobiQ₂Reflection (leftCollisionPoint μ) = -leftCollisionPoint μ := by
      funext i; fin_cases i <;> simp [jacobiQ₂Reflection, leftCollisionPoint]
    have hnp : jacobiQ₂Reflection (leftCollisionPoint μ) ∈ leftEnergyComponent μ c := by
      rw [hρp]; exact (hinv _).1 hp
    have hpre : IsPreconnected (jacobiQ₂Reflection '' leftEnergyComponent μ c) :=
      isPreconnected_connectedComponentIn.image _ reflCLM.continuous.continuousOn
    have hsub : jacobiQ₂Reflection '' leftEnergyComponent μ c ⊆ regularEnergyLocus μ c := by
      rintro _ ⟨s, hs, rfl⟩
      have hsE := connectedComponentIn_subset _ _ hs
      have h1 := hK s
      simp only [K, reflCLM_apply] at h1
      exact ⟨by rw [h1]; exact hsE.1, by rw [hD]; exact hsE.2⟩
    have := hpre.subset_connectedComponentIn ⟨_, hp, rfl⟩ hsub
    rw [← connectedComponentIn_eq hnp] at this
    intro s hs
    exact this ⟨s, hs, rfl⟩
  -- the vector field is reversed by the reflection
  have hX : ∀ s ∈ leftEnergyComponent μ c,
      hamiltonianVectorField K (jacobiQ₂Reflection s) =
        -jacobiQ₂Reflection (hamiltonianVectorField K s) := by
    intro s hs
    have hd : DifferentiableAt ℝ K (reflCLM s) :=
      (hsmooth _ (hρcomp s hs)).1.differentiableAt (by simp)
    have hp : ∀ i : Fin 4, partialDerivative K (jacobiQ₂Reflection s) i =
        fderiv ℝ K s (jacobiQ₂Reflection (coordinateVector i)) := by
      intro i
      have := fderiv_symm_apply K reflCLM hK s hd (jacobiQ₂Reflection (coordinateVector i))
      simp only [reflCLM_apply, hρρ] at this
      unfold partialDerivative
      rw [this]
    have e0 : jacobiQ₂Reflection (coordinateVector 0) = coordinateVector 0 := by
      funext j; fin_cases j <;> simp [jacobiQ₂Reflection, coordinateVector]
    have e1 : jacobiQ₂Reflection (coordinateVector 1) = -coordinateVector 1 := by
      funext j; fin_cases j <;> simp [jacobiQ₂Reflection, coordinateVector]
    have e2 : jacobiQ₂Reflection (coordinateVector 2) = -coordinateVector 2 := by
      funext j; fin_cases j <;> simp [jacobiQ₂Reflection, coordinateVector]
    have e3 : jacobiQ₂Reflection (coordinateVector 3) = coordinateVector 3 := by
      funext j; fin_cases j <;> simp [jacobiQ₂Reflection, coordinateVector]
    have q0 := hp 0; have q1 := hp 1; have q2 := hp 2; have q3 := hp 3
    rw [e0] at q0; rw [e1, map_neg] at q1; rw [e2, map_neg] at q2; rw [e3] at q3
    funext i; fin_cases i
    · show partialDerivative K _ 2 = -(partialDerivative K s 2)
      rw [q2]; rfl
    · show partialDerivative K _ 3 = -(-(partialDerivative K s 3))
      rw [q3]; simp [partialDerivative]
    · show -partialDerivative K _ 0 = -(-(-partialDerivative K s 0))
      rw [q0]; simp [partialDerivative]
    · show -partialDerivative K _ 1 = -(-partialDerivative K s 1)
      rw [q1]; simp [partialDerivative]
  have huniq := component_curves_unique μ c hμ0 hμ1 hc
    (fun u => jacobiQ₂Reflection ((φ (-u) s₁ : LeftEnergyState μ c) : Phase))
    (fun u => ((φ u s₂ : LeftEnergyState μ c) : Phase))
    (fun u => ⟨hρcomp _ (φ (-u) s₁).2, by
      have h1 := flow_line_hasDerivAt μ c φ hφ s₁ (-u)
      have h2 := h1.scomp u (hasDerivAt_neg u)
      have h3 := reflCLM.hasFDerivAt.comp_hasDerivAt u h2
      rw [hX _ (φ (-u) s₁).2]
      have h4 : HasDerivAt (fun u => jacobiQ₂Reflection ((φ (-u) s₁ : LeftEnergyState μ c) : Phase))
          (reflCLM ((-1 : ℝ) • hamiltonianVectorField K ((φ (-u) s₁ : LeftEnergyState μ c) : Phase)))
          u := h3
      refine h4.congr_deriv ?_
      rw [reflCLM_apply]
      funext i; fin_cases i <;> simp [jacobiQ₂Reflection]⟩)
    (fun u => ⟨(φ u s₂).2, flow_line_hasDerivAt μ c φ hφ s₂ u⟩)
    (by simp [hs])
  have := congrFun huniq (-t)
  simp only [neg_neg] at this
  exact this.symm
