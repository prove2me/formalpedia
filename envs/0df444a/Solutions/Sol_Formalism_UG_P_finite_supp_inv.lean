-- Prove2me | solution 1 for Formalism.UG.P.finite_supp_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:28.385642+00:00
-- url     : https://prove2.me/submissions/ca862cc8-9d6d-4d4c-ad40-f6221152c55c

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Theorems.Thm_Formalism_UG_P_orbit_coset_finite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)
private lemma smul_quotient_mk (g x : G) : (g • (x : G ⧸ K)) = ((g * x : G) : G ⧸ K) := rfl
private lemma subgroup_smul_quotient_mk (k : K) (x : G) : (k • (x : G ⧸ K)) = (((k : G) * x : G) : G ⧸ K) := rfl
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)
namespace Formalism.UG.P
theorem _root_.solution (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (g : G) :
    {y : G ⧸ K | f (y.out⁻¹ * g) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s⁻¹).image (fun y : G ⧸ K => g • y)).subset ?_
  intro y hy
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hy
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨b⁻¹ • (((s⁻¹ : G)) : G ⧸ K), ⟨b⁻¹, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk, Subgroup.coe_inv]
  rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
  have hy' : y.out = g * ((a : G) * s * b)⁻¹ := by rw [← hab]; group
  rw [hy']
  convert K.inv_mem a.2 using 1
  group
end Formalism.UG.P
