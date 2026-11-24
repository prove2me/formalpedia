-- Prove2me | solution 1 for Formalism.UG.P.stabilizer_coset_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:46.85963+00:00
-- url     : https://prove2.me/submissions/60141612-e7d2-44b6-ac40-145ffd3537d1

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
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
theorem _root_.solution (s : G) :
    MulAction.stabilizer K ((s : G ⧸ K)) = (K.map (MulAut.conj s).toMonoidHom).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map, subgroup_smul_quotient_mk,
    QuotientGroup.eq]
  constructor
  · intro hk
    refine ⟨s⁻¹ * k * s, ?_, ?_⟩
    · have := K.inv_mem hk
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨t, ht, hts⟩
    rw [← hts]
    simpa [MulAut.conj_apply, mul_assoc] using K.inv_mem ht
end Formalism.UG.P
