-- Prove2me | solution 1 for Formalism.UG.P.wlocal_map_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:46.312805+00:00
-- url     : https://prove2.me/submissions/82e13c4f-2e67-40cc-9620-efdb7f3bb403

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_map_applyWord
import Theorems.Thm_Formalism_UG_P_wlocal_map_hw
import Theorems.Thm_Formalism_UG_P_wlocal_map_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R S : Type} [CommRing R] [CommRing S]
namespace Formalism.UG.P
theorem _root_.solution (φ : R →+* S) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map φ f ∈ weyl S r n hn ν := by
  unfold weyl at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    rw [wlocal_map_applyWord, wlocal_map_hw]
    unfold weyl
    exact Submodule.subset_span ⟨w, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro m x _ hx
    rw [wlocal_map_smul]
    exact Submodule.smul_mem _ _ hx
end Formalism.UG.P
