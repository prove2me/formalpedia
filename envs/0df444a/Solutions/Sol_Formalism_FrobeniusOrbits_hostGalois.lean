-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:22:56.138977+00:00
-- url     : https://prove2.me/submissions/fe9cd712-280b-479b-a975-05228bd0b053

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hcl_eq_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galMap_zeta_inversion
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_hostE_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_finrank_cmField
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_isGalois_hostE
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_lift
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_restrict
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_galE_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Galois
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostGalois := by
  unfold HostGalois
  intro e q d hqd L _ _ ζ a b h
  haveI := (layer_galois hqd h).1
  obtain ⟨-, -, hmul, hbij⟩ := layer_galois hqd h
  refine ⟨isGalois_hostE hqd h, finrank_cmField hqd h, fun σ τ => ?_, ⟨fun σ σ' hss => ?_, fun y => ?_⟩⟩
  · obtain ⟨τ1, h1⟩ := exists_lift hqd h σ
    obtain ⟨τ2, h2⟩ := exists_lift hqd h τ
    have h12 : ∀ x : hostE ζ a b, (((σ * τ) x : hostE ζ a b) : L) = (τ1 * τ2) (x : L) := by
      intro x
      rw [AlgEquiv.mul_apply, h1, h2]
      rfl
    rw [galE_lift h h12, galE_lift h h1, galE_lift h h2, hmul]
    rfl
  · obtain ⟨τ1, h1⟩ := exists_lift hqd h σ
    obtain ⟨τ2, h2⟩ := exists_lift hqd h σ'
    rw [galE_lift h h1, galE_lift h h2] at hss
    have ha : (galMap h.1 a b τ1).2.1 = (galMap h.1 a b τ2).2.1 := congrArg (fun z => z.1.1) hss
    have hb : (galMap h.1 a b τ1).2.2 = (galMap h.1 a b τ2).2.2 := congrArg (fun z => z.1.2) hss
    have hc := (hcl_eq_iff e _ _).1 (congrArg Prod.snd hss)
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [h1, h2]
    rcases hc with hc | hc
    · have h3 : τ1 = τ2 := hbij.1 (Prod.ext hc (Prod.ext ha hb))
      rw [h3]
    · have h3 : τ1 = τ2 * tau0 hqd h := by
        apply hbij.1
        rw [hmul, galMap_zeta_inversion hqd h]
        exact Prod.ext (by rw [hc]; exact (mul_neg_one _).symm)
          (Prod.ext (ha.trans (mul_one _).symm) (hb.trans (mul_one _).symm))
      rw [h3, AlgEquiv.mul_apply, (mem_hostE_iff hqd h _).1 x.2]
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective y.2
    obtain ⟨τ, hτ⟩ := hbij.2 ((u, y.1.1, y.1.2) : GalL (e + 2))
    obtain ⟨σ, hσ⟩ := exists_restrict hqd h τ
    refine ⟨σ, ?_⟩
    rw [galE_lift h hσ, hτ]
    exact Prod.ext rfl hu
end Formalism.FrobeniusOrbits
