-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostRamified_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:53.828522+00:00
-- url     : https://prove2.me/submissions/060f4898-6a4b-4c72-92d2-06b0522acdce

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_ne_one_of_galE
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


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
open Formalism.TwoAdicCyclotomicDecomposition
open Misc2
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hI : HostInertia) : HostRamified := by
  intro e q d he hH L _ _ ζ a b h p _ P _ _
  have hqd := hH.toHypOdd
  obtain ⟨-, -, -, hbij⟩ := hostGalois e q d hqd L ζ a b h
  constructor
  · rintro ⟨σ, hσ1, hσ⟩
    by_contra hp
    push Not at hp
    obtain ⟨hp2, hpq, hpd⟩ := hp
    have hF := hostFrob_of hostGalois hostGalSpec e q d hqd L ζ a b h p hp2 hpq hpd P
    exact hσ1 ((hF.2.2 σ).mp hσ)
  · rintro (rfl | rfl | rfl)
    · obtain ⟨σ, hσ⟩ := hbij.2 (((1, 1), hcl e (u5 (e + 2))) : GG e)
      refine ⟨σ, ne_one_of_galE hqd h σ ?_, ?_⟩
      · rw [hσ]
        intro h1
        have h2 : hcl e (u5 (e + 2)) = 1 := congrArg Prod.snd h1
        have h3 := (hostGroup e).2.2.2.2.2.2.2.1
        rw [h2, orderOf_one] at h3
        have : 2 ≤ 2 ^ e := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
        omega
      · have : P.LiesOver (span {(2 : ℤ)}) := by simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
        exact ((hI e q d hH L ζ a b h σ).1 P).mpr (by rw [hσ]; rfl)
    · obtain ⟨σ, hσ⟩ := hbij.2 (sg e)
      refine ⟨σ, ne_one_of_galE hqd h σ ?_, ?_⟩
      · rw [hσ]; simp [sg, Prod.ext_iff]
      · exact ((hI e p d hH L ζ a b h σ).2.1 P).mpr (Or.inr hσ)
    · obtain ⟨σ, hσ⟩ := hbij.2 (((1, -1), 1) : GG e)
      refine ⟨σ, ne_one_of_galE hqd h σ ?_, ?_⟩
      · rw [hσ]; simp [Prod.ext_iff]
      · exact ((hI e q p hH L ζ a b h σ).2.2 P).mpr (Or.inr hσ)
end Formalism.FrobeniusOrbits
