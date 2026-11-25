-- Prove2me | solution 1 for BayesianPersuasion.Proof.concavification_max_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:11:04.841108+00:00
-- url     : https://prove2.me/submissions/dfa746fe-7ece-4d84-b92c-d9b31d6b8d10

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment
public import Theorems.Thm_BayesianPersuasion_Proof_sender_pair_mem
public import Theorems.Thm_BayesianPersuasion_Proof_hull_compact

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
    (p.val, concavification u v p.val) ∈ convexHull ℝ (bestReplyPayoffs u v) := by
  let K := convexHull ℝ (bestReplyPayoffs u v) ∩ {x | x.1 = p.val}
  have hk : IsCompact K := (hull_compact u v hu hv).inter_right
    (isClosed_eq continuous_fst continuous_const)
  have hne : K.Nonempty :=
    ⟨(p.val, senderPayoff u v p), subset_convexHull ℝ _ (sender_pair_mem u v hu hv p), rfl⟩
  obtain ⟨x, hx, hm⟩ := hk.exists_isMaxOn hne continuous_snd.continuousOn
  have hxp : x = (p.val, x.2) := Prod.ext hx.2 rfl
  have hf : concavification u v p.val = x.2 := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨x.2, hxp ▸ hx.1⟩
    · intro z hz
      exact hm ⟨hz, rfl⟩
    · intro z hz
      exact ⟨x.2, hxp ▸ hx.1, hz⟩
  rw [hf, ← hx.2]
  exact hx.1
end BayesianPersuasion.Proof
