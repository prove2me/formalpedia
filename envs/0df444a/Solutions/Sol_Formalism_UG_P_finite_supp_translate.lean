-- Prove2me | solution 1 for Formalism.UG.P.finite_supp_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:28.98687+00:00
-- url     : https://prove2.me/submissions/53382f20-6c22-47ff-b44d-1f56978db477

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
    (hf : FinDosetSupp K f) (h : G) :
    {x : G ⧸ K | f (h * x.out) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s).image (fun y : G ⧸ K => h⁻¹ • y)).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a • ((s : G ⧸ K)), ⟨a, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk]
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  have hx' : x.out = h⁻¹ * ((a : G) * s * b) := by rw [← hab]; group
  rw [hx']
  convert b.2 using 1
  group
end Formalism.UG.P
