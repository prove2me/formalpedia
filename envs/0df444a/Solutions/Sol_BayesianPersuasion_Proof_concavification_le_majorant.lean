-- Prove2me | solution 1 for BayesianPersuasion.Proof.concavification_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:14:02.112258+00:00
-- url     : https://prove2.me/submissions/e7bf619d-0d8e-42cb-a575-7d54f1d025f1

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_optimal_split

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
namespace BayesianPersuasion.Proof
theorem _root_.solution (g : (Ω → ℝ) → ℝ)
    (hg : ConcaveOn ℝ (probabilitySimplex Ω) g)
    (hmajor : ∀ p : Belief Ω, senderPayoff u v p ≤ g p.val) (p : Belief Ω) :
    concavification u v p.val ≤ g p.val := by
  obtain ⟨k, _, w, b, hb, hval⟩ := optimal_split u v hu hv p
  have hbar : ∑ s, w.val s • (b s).val = p.val := by
    ext ω
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hb ω
  have hj := hg.le_map_sum (t := Finset.univ) (w := w.val) (p := fun s => (b s).val)
    (fun s _ => w.property.1 s) w.property.2 (fun s _ => (b s).property)
  rw [hbar] at hj
  rw [← hval]
  exact (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (hmajor (b s)) (w.property.1 s)).trans hj
end BayesianPersuasion.Proof
