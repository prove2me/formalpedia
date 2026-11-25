-- Prove2me | solution 1 for BayesianPersuasion.Proof.probabilitySimplex_convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:46.946099+00:00
-- url     : https://prove2.me/submissions/74bfe0db-c5a3-4928-93aa-9ef8abc08f67

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof
variable [TopologicalSpace A] [CompactSpace A] [Nonempty A] [T2Space A]
variable (u v : A → Ω → ℝ)
variable (hu : ∀ ω, Continuous (fun a => u a ω))
variable (hv : ∀ ω, Continuous (fun a => v a ω))
include hu hv
omit hu hv
namespace BayesianPersuasion.Proof
theorem _root_.solution : Convex ℝ (probabilitySimplex Ω) := by
  intro p hp q hq a b ha hb hab
  constructor
  · intro ω
    exact add_nonneg (mul_nonneg ha (hp.1 ω)) (mul_nonneg hb (hq.1 ω))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
    simpa using hab
end BayesianPersuasion.Proof
