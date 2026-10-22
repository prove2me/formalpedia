-- Prove2me | solution 1 for BirkhoffGlobalSection.variational_flow_period_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-30T23:32:36.776107+00:00
-- url     : https://prove2.me/submissions/c3a75ca9-b508-49d0-9f42-9579a3896cbb

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Periodicity of a closed orbit and the period cocycle of its variational flow

Let `x` solve Hamilton's equations for a function `F` that is smooth along `x`, with
`x T = x 0`. The Hamiltonian field is `C¹`, hence locally Lipschitz, near every point of
the orbit, so `t ↦ x (t + T)` and `x` solve the same equation with the same initial
value; uniqueness, applied through a clopen argument, gives `x (t + T) = x t`.

The coefficient `A t = D X_F (x t)` of the variational equation is then continuous and
`T`-periodic. Both `t ↦ Y (t + T)` and `t ↦ Y t ∘ Y T` solve `U' = A ∘ U` with value
`Y T` at `0`. The right-hand side is Lipschitz in `U` with constant `‖A t‖`, which is
locally bounded, so the same clopen argument gives `Y (t + T) = Y t ∘ Y T`.
-/

open BirkhoffGlobalSection
open scoped ContDiff Topology

set_option autoImplicit false

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

/-- Uniqueness for the linear equation `U' = A ∘ U` with continuous coefficient. -/
private lemma linear_unique {A : ℝ → (Phase →L[ℝ] Phase)} (hA : Continuous A)
    {Z W : ℝ → (Phase →L[ℝ] Phase)}
    (hZ : ∀ t, HasDerivAt Z ((A t).comp (Z t)) t)
    (hW : ∀ t, HasDerivAt W ((A t).comp (W t)) t) (h0 : Z 0 = W 0) :
    ∀ t, Z t = W t := by
  have hZc : Continuous Z := continuous_iff_continuousAt.2 fun t => (hZ t).continuousAt
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  set E : Set ℝ := {t | Z t = W t} with hE
  have hclosed : IsClosed E := isClosed_eq hZc hWc
  have hopen : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have ht₀' : Z t₀ = W t₀ := ht₀
    set K : NNReal := ⟨‖A t₀‖ + 1, by positivity⟩ with hK
    have hb : (fun t => ‖A t‖) ⁻¹' Set.Iio (‖A t₀‖ + 1) ∈ 𝓝 t₀ :=
      hA.norm.continuousAt (Iio_mem_nhds (lt_add_one _))
    have hL : ∀ᶠ t in 𝓝 t₀,
        LipschitzOnWith K (fun U : Phase →L[ℝ] Phase => (A t).comp U) Set.univ := by
      filter_upwards [hb] with t ht
      have ht' : ‖A t‖ < ‖A t₀‖ + 1 := ht
      apply LipschitzOnWith.of_dist_le_mul
      intro U _ U' _
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      calc ‖(A t).comp (U - U')‖ ≤ ‖A t‖ * ‖U - U'‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖A t₀‖ + 1) * ‖U - U'‖ := by gcongr
        _ = K * ‖U - U'‖ := by rw [hK]; rfl
    have heq := ODE_solution_unique_of_eventually
      (v := fun t U => (A t).comp U) (s := fun _ => Set.univ) (K := K) hL
      (Filter.Eventually.of_forall fun t => ⟨hZ t, trivial⟩)
      (Filter.Eventually.of_forall fun t => ⟨hW t, trivial⟩) ht₀'
    filter_upwards [heq] with t ht
    exact ht
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0⟩
  intro t
  have ht : t ∈ E := by rw [huniv]; trivial
  exact ht

theorem solution
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hF : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t))
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y) :
    (∀ t : ℝ, x (t + T) = x t) ∧
      ∀ t : ℝ, Y (t + T) = (Y t).comp (Y T) := by
  obtain ⟨-, -, hder, hclose⟩ := hx
  obtain ⟨hY0, hYd⟩ := hY
  have hF2 : ∀ t, ContDiffAt ℝ 2 F (x t) := fun t =>
    (hF t).of_le (WithTop.coe_le_coe.2 le_top)
  have hper : ∀ t, x (t + T) = x t :=
    periodic_of_closed (fun t => (hvf_contDiffAt (hF2 t)).exists_lipschitzOnWith) hder hclose
  refine ⟨hper, ?_⟩
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  set A : ℝ → (Phase →L[ℝ] Phase) := fun t => fderiv ℝ (hamiltonianVectorField F) (x t)
    with hAdef
  have hA : Continuous A := continuous_iff_continuousAt.2 fun t =>
    ContinuousAt.comp (g := fderiv ℝ (hamiltonianVectorField F))
      (((hvf_contDiffAt (hF2 t)).fderiv_right (m := 0) (by norm_num)).continuousAt) hxc.continuousAt
  have hZ : ∀ t, HasDerivAt (fun t => Y (t + T)) ((A t).comp (Y (t + T))) t := by
    intro t
    have h := HasDerivAt.comp_add_const t T (hYd (t + T))
    rw [hper t] at h
    exact h
  have hW : ∀ t, HasDerivAt (fun t => (Y t).comp (Y T)) ((A t).comp ((Y t).comp (Y T))) t := by
    intro t
    have h := (hYd t).clm_comp (hasDerivAt_const t (Y T))
    refine h.congr_deriv ?_
    simp [hAdef, ContinuousLinearMap.comp_assoc]
  have h0 : (fun t => Y (t + T)) 0 = (fun t => (Y t).comp (Y T)) 0 := by
    simp [hY0]
  exact linear_unique hA hZ hW h0
