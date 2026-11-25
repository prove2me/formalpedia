-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.norm_cmF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:26.976669+00:00
-- url     : https://prove2.me/submissions/e3fda786-e72e-448b-9d69-7b0f1f2a3f2f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjF_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_finrank_cmF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gal_cmF_cases
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_one_ne_conjF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (x : K) :
    ((Algebra.norm (cmF K) x : cmF K) : K) = x * star x := by
  classical
  haveI : IsGalois (cmF K) K := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [finrank_cmF hK, Nat.card_eq_fintype_card]
    apply le_antisymm
    · convert (AlgEquiv.card_le (F := cmF K) (K := K)).trans (finrank_cmF hK).le
    · have := Finset.card_le_univ ({1, conjF K} : Finset (K ≃ₐ[cmF K] K))
      rwa [Finset.card_pair (one_ne_conjF hK)] at this
  show algebraMap (cmF K) K (Algebra.norm (cmF K) x) = _
  rw [Algebra.norm_eq_prod_automorphisms]
  have hu : (Finset.univ : Finset (K ≃ₐ[cmF K] K)) = {1, conjF K} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact gal_cmF_cases hK g
  rw [hu, Finset.prod_pair (one_ne_conjF hK), AlgEquiv.one_apply, conjF_apply]
end Formalism.HermitianLattices.Ext.L3
