-- Prove2me | solution 1 for BayesianPersuasion.Proof.split_pair_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:56.861372+00:00
-- url     : https://prove2.me/submissions/b639c6af-1a32-4e4a-bc3d-276b34c838b7

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_sender_pair_mem

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
theorem _root_.solution (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) :
    (p.val, splitValue u v w b) ∈ convexHull ℝ (bestReplyPayoffs u v) := by
  apply mem_convexHull_of_exists_fintype w.val
    (fun s => ((b s).val, senderPayoff u v (b s))) w.property.1 w.property.2
    (fun j => sender_pair_mem u v hu hv (b j))
  apply Prod.ext
  · ext ω
    simpa only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hb ω
  · simp [splitValue, Prod.snd_sum, Prod.smul_snd]
end BayesianPersuasion.Proof
