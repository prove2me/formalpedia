-- Prove2me | solution 1 for FD1D.FiniteKernel.exists_stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:39.418804+00:00
-- url     : https://prove2.me/submissions/70f3aefa-041f-4e40-9b73-a8034a4f0daa

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
import Theorems.Thm_FD1D_FiniteKernel_tendsto_cesaro_error
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
    (K : FiniteKernel α) :
    ∃ μ : FiniteLaw α, K.IsStationary μ := by
  let μ0 : FiniteLaw α := FiniteLaw.dirac (Classical.arbitrary α)
  let A : ℕ → α → ℝ := fun n => (K.cesaroLaw μ0 n).mass
  have hA (n : ℕ) : A n ∈ stdSimplex ℝ α :=
    ⟨(K.cesaroLaw μ0 n).mass_nonneg, (K.cesaroLaw μ0 n).sum_mass⟩
  obtain ⟨v, hv, φ, hφ, hlim⟩ :=
    (isCompact_stdSimplex ℝ α).tendsto_subseq hA
  let π : FiniteLaw α := ⟨v, hv.1, hv.2⟩
  refine ⟨π, ?_⟩
  have hlim' : Tendsto (fun n => A (φ n)) atTop (𝓝 v) := by
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
end FD1D.FiniteKernel
