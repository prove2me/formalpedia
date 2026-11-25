-- Prove2me | solution 1 for Formalism.L2.SG.Pf.HasProdFiniteSupport.hasProd_compl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:13:21.002021+00:00
-- url     : https://prove2.me/submissions/0abb85fc-9c7b-4609-9893-8e34ee107282

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HasProdFiniteSupport
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_HasProdFiniteSupport_hasProd_inv___2cdd04f14e39

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.HasProdFiniteSupport
open Filter Topology
variable {ι : Type*}
namespace Formalism.L2.SG.Pf.HasProdFiniteSupport
theorem _root_.solution (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd f a) (hf : ∀ i, P i → f i ≠ 0) :
    HasProd (fun i : {i // ¬ P i} => f i) (a * (∏ i : {i // P i}, f i)⁻¹) := by
  have h2 : HasProd (fun i => ({i | P i}.mulIndicator f i)⁻¹) (∏ i : {i // P i}, f i)⁻¹ := by
    have h0 : HasProd ({i | P i}.mulIndicator f) (∏ i : {i // P i}, f i) :=
      letI : Fintype ({i | P i} : Set ι) := inferInstanceAs (Fintype {i // P i})
    (hasProd_subtype_iff_mulIndicator (s := {i | P i})).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ({i | ¬ P i}.mulIndicator f) (a * (∏ i : {i // P i}, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : P i
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := {i | ¬ P i})).mpr h4
end Formalism.L2.SG.Pf.HasProdFiniteSupport
