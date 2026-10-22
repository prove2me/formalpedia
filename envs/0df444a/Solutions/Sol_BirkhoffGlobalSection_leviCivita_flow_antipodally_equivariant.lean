-- Prove2me | solution 1 for BirkhoffGlobalSection.leviCivita_flow_antipodally_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T23:46:11.265193+00:00
-- url     : https://prove2.me/submissions/b5013ba4-081a-4512-b063-f9341c769081

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

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    IsAntipodallyEquivariantFlow μ c φ := by
  obtain ⟨heven, hinv, -⟩ := antipodal_symmetry μ c hμ0 hμ1 hc
  obtain ⟨-, hsmooth, -, -, -⟩ := left_energy_component_geometry μ c hμ0 hμ1 hc
  set K := leviCivitaHamiltonian μ c
  set L : Phase →L[ℝ] Phase := -ContinuousLinearMap.id ℝ Phase
  have hL : ∀ s, K (L s) = K s := fun s => by simp [L, K, heven]
  -- the vector field is odd on the component
  have hX : ∀ s ∈ leftEnergyComponent μ c,
      hamiltonianVectorField K (-s) = -hamiltonianVectorField K s := by
    intro s hs
    have hd : DifferentiableAt ℝ K (L s) := by
      have := (hsmooth (-s) ((hinv s).1 hs)).1.differentiableAt (by simp)
      simpa [L] using this
    have hp : ∀ i : Fin 4, partialDerivative K (-s) i = -partialDerivative K s i := by
      intro i
      have := fderiv_symm_apply K L hL s hd (-coordinateVector i)
      simp only [L, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, neg_neg,
        map_neg] at this
      unfold partialDerivative
      linarith
    funext i; fin_cases i <;> simp [hamiltonianVectorField, hp]
  intro t s₁ s₂ hs
  have huniq := component_curves_unique μ c hμ0 hμ1 hc
    (fun u => -((φ u s₁ : LeftEnergyState μ c) : Phase))
    (fun u => ((φ u s₂ : LeftEnergyState μ c) : Phase))
    (fun u => ⟨(hinv _).1 (φ u s₁).2, by
      have := (flow_line_hasDerivAt μ c φ hφ s₁ u).neg
      rw [← hX _ (φ u s₁).2] at this
      exact this⟩)
    (fun u => ⟨(φ u s₂).2, flow_line_hasDerivAt μ c φ hφ s₂ u⟩)
    (by simp [hs])
  have := congrFun huniq t
  exact this.symm
