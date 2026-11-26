-- Prove2me | solution 1 for FD1D.FiniteKernel.exists_stationary_groupInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:32.012857+00:00
-- url     : https://prove2.me/submissions/aa7f5628-0ce2-4d16-9fff-ba7af5b16394

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_tendsto_cesaro_error
import Theorems.Thm_FD1D_FiniteKernel_uniform_groupInvariant
import Theorems.Thm_FD1D_FiniteKernel_cesaroLaw_groupInvariant
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]
namespace FD1D.FiniteKernel
theorem _root_.solution [DecidableEq α] [Nonempty α]
    {G : Type*} [Group G] [Fintype G]
    (ρ : G →* Equiv.Perm α) (K : FiniteKernel α)
    (hK : GroupEquivariant ρ K) :
    ∃ μ : FiniteLaw α, K.IsStationary μ ∧ GroupInvariant ρ μ := by
  let μ0 : FiniteLaw α := FiniteLaw.uniform
  let A : ℕ → α → ℝ := fun n => (K.cesaroLaw μ0 n).mass
  have hμ0 : GroupInvariant ρ μ0 :=
    uniform_groupInvariant ρ
  have hA (n : ℕ) : A n ∈ stdSimplex ℝ α :=
    ⟨(K.cesaroLaw μ0 n).mass_nonneg, (K.cesaroLaw μ0 n).sum_mass⟩
  have hAinv (n : ℕ) : GroupInvariant ρ (K.cesaroLaw μ0 n) :=
    cesaroLaw_groupInvariant ρ hK hμ0 n
  obtain ⟨v, hv, φ, hφ, hlim⟩ :=
    (isCompact_stdSimplex ℝ α).tendsto_subseq hA
  let π : FiniteLaw α := ⟨v, hv.1, hv.2⟩
  refine ⟨π, ?_, ?_⟩
  · have hlim' : Tendsto (fun n => A (φ n)) atTop (𝓝 v) := by
      simpa only [Function.comp_def] using hlim
    have hcont : Continuous (fun w : α → ℝ => w ᵥ* K.matrix) := by
      fun_prop
    have hstep :
        Tendsto (fun n => A (φ n) ᵥ* K.matrix) atTop
          (𝓝 (v ᵥ* K.matrix)) :=
      (hcont.tendsto v).comp hlim'
    have hdiff :
        Tendsto (fun n => A (φ n) ᵥ* K.matrix - A (φ n)) atTop
          (𝓝 (v ᵥ* K.matrix - v)) :=
      hstep.sub hlim'
    have herr :
        Tendsto (fun n => A (φ n) ᵥ* K.matrix - A (φ n)) atTop
          (𝓝 0) := by
      simpa [A, cesaroLaw, Function.comp_def] using
        (K.tendsto_cesaro_error μ0).comp hφ.tendsto_atTop
    have hz : v ᵥ* K.matrix - v = 0 :=
      tendsto_nhds_unique hdiff herr
    have hvec : v ᵥ* K.matrix = v := sub_eq_zero.mp hz
    apply FiniteLaw.ext
    intro y
    have hy := congrFun hvec y
    simpa [IsStationary, step, π, Matrix.vecMul, dotProduct, matrix] using hy
  · intro g x
    have hlim' : Tendsto (fun n => A (φ n)) atTop (𝓝 v) := by
      simpa only [Function.comp_def] using hlim
    have hleft :=
      (tendsto_pi_nhds.mp hlim') ((ρ g) x)
    have hright :=
      (tendsto_pi_nhds.mp hlim') x
    have hseq :
        (fun n => A (φ n) ((ρ g) x)) =
          (fun n => A (φ n) x) := by
      funext n
      exact hAinv (φ n) g x
    rw [hseq] at hleft
    exact tendsto_nhds_unique hleft hright
end FD1D.FiniteKernel
