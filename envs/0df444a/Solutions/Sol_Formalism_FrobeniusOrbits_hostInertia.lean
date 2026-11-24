-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostInertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:49:30.110806+00:00
-- url     : https://prove2.me/submissions/28031769-9c72-49ab-a80b-45310bb7f5db

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_hcl_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sub_h
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sign_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_sup
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTame
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTwo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Inertia
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostInertia := by
  intro e q d hH L _ _ ζ a b h σ
  have hqd := hH.toHypOdd
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have hQD : HypQD q d := ⟨hH.1, hH.2.1, hH.2.2.1, by have := hH.2.2.2.1; omega⟩
  have hspec := hostGalSpec e q d hqd L ζ a b h σ
  have hsa := hspec.1
  have hsb := hspec.2.1
  have hn : 1 ≤ e + 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro P _ _
    haveI : P.LiesOver (span {((2 : ℕ) : ℤ)}) := by simpa using ‹P.LiesOver (span {(2 : ℤ)})›
    constructor
    · intro hall
      have h1 := sign_one (aE ζ a b) ((galE e ζ a b σ).1.1) σ hsa hqd.1 hq4 h.2.1 Nat.prime_two
        (Ne.symm hqd.2.2.2.1) P hall
      have h2 := sign_one (bE ζ a b) ((galE e ζ a b σ).1.2) σ hsb hqd.2.1 hd4 h.2.2.1 Nat.prime_two
        (Ne.symm hqd.2.2.2.2) P hall
      exact Prod.ext h1 h2
    · intro h1
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (galE e ζ a b σ).2
      refine sup hqd h 2 P σ (m, 1, 1) ?_ ?_
      · exact Prod.ext h1 hm.symm
      · intro τ hτ Q _ _
        refine ((layerInertiaTwo (e + 2) q d hn hQD L ζ a b h Q τ).2 ?_)
        show (galMap h.1 a b τ).2 = 1
        rw [hτ]
        rfl
  · intro P _ _
    constructor
    · intro hall
      have hh := sub_h hqd h q hqd.1 hqd.2.2.2.1 P σ hall
      have h2 := sign_one (bE ζ a b) ((galE e ζ a b σ).1.2) σ hsb hqd.2.1 hd4 h.2.2.1 hqd.1
        hqd.2.2.1 P hall
      rcases Int.units_eq_one_or (galE e ζ a b σ).1.1 with h1 | h1
      · left
        exact Prod.ext (Prod.ext h1 h2) hh
      · right
        exact Prod.ext (Prod.ext h1 h2) hh
    · intro hg
      rcases hg with hg | hg
      · refine sup hqd h q P σ 1 ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).1 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.one_mem _
      · refine sup hqd h q P σ (1, -1, 1) ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).1 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.mem_zpowers _
  · intro P _ _
    constructor
    · intro hall
      have hh := sub_h hqd h d hqd.2.1 hqd.2.2.2.2 P σ hall
      have h1 := sign_one (aE ζ a b) ((galE e ζ a b σ).1.1) σ hsa hqd.1 hq4 h.2.1 hqd.2.1
        (Ne.symm hqd.2.2.1) P hall
      rcases Int.units_eq_one_or (galE e ζ a b σ).1.2 with h2 | h2
      · left
        exact Prod.ext (Prod.ext h1 h2) hh
      · right
        exact Prod.ext (Prod.ext h1 h2) hh
    · intro hg
      rcases hg with hg | hg
      · refine sup hqd h d P σ 1 ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).2 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.one_mem _
      · refine sup hqd h d P σ (1, 1, -1) ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).2 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.mem_zpowers _
end Formalism.FrobeniusOrbits
