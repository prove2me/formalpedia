-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.propLocCont_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:18.856507+00:00
-- url     : https://prove2.me/submissions/0fa4881f-1c8f-4bc1-8ee6-6aa1ead998cc

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_PropLoc
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_HOneTorsionFree
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_smul_bij
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_h_one_torsion_free
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_pi_torsion
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_propLoc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
open ReciprocityTheory.Gal
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution (hConn : StatConnTors.{u}) (hEmb : StatQuotEmbeds.{u})
    (hDual : StatDualLattice.{u}) : StatPropLocCont.{u} := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D HfV HfV' ℓ e' ι₁ ι₂ P Q
    hT hperf hfin hc hBK hP hQ
  have h1 := hDual O G VT VT' D.ε D.ρT D.ρT' D.bT D.T hT D.stT hperf D.eqT
  have hT' : IsLatticeIn D.T' := h1.1
  have hrk : Module.finrank O D.T' = Module.finrank O D.T := h1.2.1
  obtain ⟨e, he⟩ : ∃ e : (VT' ⧸ D.T') →ₗ[O] (Fin (Module.finrank O D.T) → KO O),
      Function.Injective e := hrk ▸ (hEmb O VT' D.T' hT').2
  have htf : Module.IsTorsionFree O (H1 D.ρT') := h_one_torsion_free D.ρT' (fun c hc => smul_bij c hc)
  have a1 : ∀ a : VT' ⧸ D.T', ∃ c : O, c ≠ 0 ∧ c • a = 0 := by
    intro a
    obtain ⟨c, hc, h⟩ := pi_torsion (e a)
    refine ⟨c, hc, he ?_⟩
    rw [map_smul, h, map_zero]
  have a2 : LinearMap.ker D.T'.mkQ = LinearMap.range D.T'.subtype := by
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  have a3 : ∀ (g : G) (m : D.T'), D.T'.subtype (D.ρTl' g m) = D.ρT' g (D.T'.subtype m) :=
    fun _ _ => rfl
  have a4 : ∀ (g : G) (m : VT'), D.T'.mkQ (D.ρT' g m) = D.ρA' g (D.T'.mkQ m) := fun _ _ => rfl
  have a5 : Topology.IsEmbedding D.T'.subtype := Topology.IsEmbedding.subtypeVal
  have hC := hConn O G D.T' VT' (VT' ⧸ D.T') D.ρTl' D.ρT' D.ρA' D.T'.subtype D.T'.mkQ
    a5 a3 a4 (Submodule.mkQ_surjective _) a2 D.contT' (fun c hc => smul_bij c hc) a1
  obtain ⟨δ, hδ⟩ := hC
  let ι : H0 D.ρA' →ₗ[O] (Fin (Module.finrank O D.T) → KO O) := e ∘ₗ (H0 D.ρA').subtype
  have hι : Function.Injective ι := he.comp (Submodule.injective_subtype _)
  let δ' : LinearMap.range ι →ₗ[O] H1 D.ρTl' := δ ∘ₗ (LinearEquiv.ofInjective ι hι).symm.toLinearMap
  have hδ' : LinearMap.range δ' = Submodule.torsion O (H1 D.ρTl') := by
    rw [← hδ]
    exact LinearEquiv.range_comp _ _
  have main := propLoc O (H1 D.ρA) (H1 D.ρT) (H1 D.ρTl') (H1 D.ρT') D.q D.j' D.pr HfV HfV' ℓ e'
    (Module.finrank O D.T) (LinearMap.range ι) δ' ι₁ ι₂ (fun i => (P i).toDirect)
    (fun i => (Q i).toDual hc) hBK hδ' hP hQ
  refine ⟨main.1, main.2.1, ?_⟩
  exact main.2.2
end Formalism.RepresentationBoundsCohomology.LOC
