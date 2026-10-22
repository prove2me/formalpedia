-- Prove2me | solution 1 for BirkhoffGlobalSection.periodic_hamiltonian_solution_shift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-01T23:24:39.936869+00:00
-- url     : https://prove2.me/submissions/2e15ad26-79db-47e4-954e-8f0763a0139d

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace BirkhoffGlobalSection

open Filter Topology

theorem leviCivitaHamiltonian_contDiffAt (μ c : ℝ) {y : Phase}
    (hy : 0 < secondCollisionDistanceSq y) :
    ContDiffAt ℝ ⊤ (leviCivitaHamiltonian μ c) y := by
  have hd : ContDiff ℝ ⊤ secondCollisionDistanceSq := by
    unfold secondCollisionDistanceSq; fun_prop
  have hs : ContDiffAt ℝ ⊤ (fun s => Real.sqrt (secondCollisionDistanceSq s)) y :=
    hd.contDiffAt.sqrt hy.ne'
  have hpos : Real.sqrt (secondCollisionDistanceSq y) ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  unfold leviCivitaHamiltonian wNormSq zNormSq
  refine ContDiffAt.sub ?_ ((contDiffAt_const.mul (by fun_prop)).div hs hpos)
  fun_prop

theorem leviCivitaField_contDiffAt (μ c : ℝ) {y : Phase}
    (hy : 0 < secondCollisionDistanceSq y) :
    ContDiffAt ℝ 1 (hamiltonianVectorField (leviCivitaHamiltonian μ c)) y := by
  have hF := (leviCivitaHamiltonian_contDiffAt μ c hy).fderiv_right (m := 1) (by simp)
  have hp : ∀ i : Fin 4,
      ContDiffAt ℝ 1 (fun s => partialDerivative (leviCivitaHamiltonian μ c) s i) y :=
    fun i => hF.clm_apply contDiffAt_const
  rw [contDiffAt_pi]
  intro j
  fin_cases j
  · exact hp 2
  · exact hp 3
  · exact (hp 0).neg
  · exact (hp 1).neg

theorem periodic_hamiltonian_solution_shift_aux
    (μ c : ℝ) (x : ℝ → Phase) (T : ℝ)
    (hmem : ∀ t : ℝ, x t ∈ leftEnergyComponent μ c)
    (hsol : ∀ t : ℝ, HasDerivAt x
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (x t)) t)
    (hper : x T = x 0) :
    ∀ s : ℝ, x (s + T) = x s := by
  set X := hamiltonianVectorField (leviCivitaHamiltonian μ c)
  set g : ℝ → Phase := fun t => x (t + T)
  have hg : ∀ t, HasDerivAt g (X (g t)) t := fun t => by
    simpa [g] using HasDerivAt.comp_add_const t T (hsol (t + T))
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hsol t).continuousAt
  have hgc : Continuous g := hxc.comp (continuous_add_const T)
  have hreg : ∀ t, 0 < secondCollisionDistanceSq (x t) := fun t =>
    (connectedComponentIn_subset _ _ (hmem t)).2
  set E : Set ℝ := {s | g s = x s}
  have hclosed : IsClosed E := isClosed_eq hgc hxc
  have hopen : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro s0 hs0
    obtain ⟨K, U, hU, hL⟩ :=
      ContDiffAt.exists_lipschitzOnWith (leviCivitaField_contDiffAt μ c (hreg s0))
    have hxU : ∀ᶠ t in 𝓝 s0, x t ∈ U := hxc.continuousAt.preimage_mem_nhds hU
    have hgU : ∀ᶠ t in 𝓝 s0, g t ∈ U := by
      have : g s0 = x s0 := hs0
      exact hgc.continuousAt.preimage_mem_nhds (this ▸ hU)
    have := ODE_solution_unique_of_eventually (v := fun _ => X) (s := fun _ => U)
      (Eventually.of_forall fun _ => hL)
      (hgU.mono fun t ht => ⟨hg t, ht⟩) (hxU.mono fun t ht => ⟨hsol t, ht⟩) hs0
    exact this
  have hE : E = Set.univ :=
    (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, by simp [E, g, hper]⟩)
  intro s
  have : s ∈ E := hE ▸ Set.mem_univ s
  exact this

end BirkhoffGlobalSection

open BirkhoffGlobalSection in
theorem solution
    (μ c : ℝ) (x : ℝ → Phase) (T : ℝ)
    (hmem : ∀ t : ℝ, x t ∈ leftEnergyComponent μ c)
    (hsol : ∀ t : ℝ, HasDerivAt x
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (x t)) t)
    (hper : x T = x 0) :
    ∀ s : ℝ, x (s + T) = x s :=
  periodic_hamiltonian_solution_shift_aux μ c x T hmem hsol hper
