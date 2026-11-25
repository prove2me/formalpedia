-- Prove2me | solution 1 for BayesianPersuasion.Proof.optimal_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:13:15.791465+00:00
-- url     : https://prove2.me/submissions/46b3a6c5-6fe0-4e05-8702-7a0f8254399c

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_concavification_max_point
public import Theorems.Thm_BayesianPersuasion_Proof_split_le_concavification
public import Theorems.Thm_BayesianPersuasion_Proof_bestReply_le_senderPayoff
public import Theorems.Thm_BayesianPersuasion_Proof_convexHull_finite_support


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
theorem _root_.solution (p : Belief Ω) :
    ∃ (k : ℕ) (_ : k ≤ Fintype.card Ω + 2) (w : Belief (Fin k))
      (b : Fin k → Belief Ω), BayesPlausible p w b ∧
        splitValue u v w b = concavification u v p.val := by
  obtain ⟨k, hk, z, w, hz, hbar⟩ := convexHull_finite_support
    (concavification_max_point u v hu hv p)
  have hreps : ∀ j, ∃ x : Belief Ω × A,
      BestReply u x.1 x.2 ∧ (x.1.val, expected v x.1 x.2) = z j := hz
  choose x hx heq using hreps
  let b := fun j => (x j).1
  have hfst : ∑ j, w.val j • (b j).val = p.val := by
    have h := congrArg Prod.fst hbar
    simpa only [Prod.fst_sum, Prod.smul_fst, ← heq, b] using h
  have hb : BayesPlausible p w b := by
    intro ω
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hfst ω
  have hsnd : ∑ j, w.val j * expected v (b j) (x j).2 = concavification u v p.val := by
    have h := congrArg Prod.snd hbar
    simpa only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, ← heq, b] using h
  refine ⟨k, by simpa [Module.finrank_prod, Module.finrank_pi] using hk, w, b, hb,
    le_antisymm (split_le_concavification u v hu hv p w b hb) ?_⟩
  rw [← hsnd]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (bestReply_le_senderPayoff u v hu hv (b j) (hx j)) (w.property.1 j)
end BayesianPersuasion.Proof
