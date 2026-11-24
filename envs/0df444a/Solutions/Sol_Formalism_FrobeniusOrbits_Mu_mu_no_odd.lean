-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Mu.mu_no_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:04.936087+00:00
-- url     : https://prove2.me/submissions/9b1ebee4-9c32-4744-a1f3-1b0b57a7e19b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_le_ram
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_mem_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_ram_bound
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
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
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]
variable {e q d : ℕ} {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Mu
theorem _root_.solution (hq : HostHyp q d) (hq3 : q ≠ 3) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (η : L) (hη : IsPrimitiveRoot η p) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) (span {(p : ℤ)})
  haveI := hQmax.isPrime
  haveI := hQover
  have h1 := mu_mem_pow p Q η hη
  have h2 := mu_le_ram p Q (p - 1) h1
  have h3 := mu_ram_bound hq.toHypOdd h p hp2 Q
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h31 := h3.1
  have hle : p ≤ 3 := by omega
  have hpq : p ≠ q := by omega
  have hpd : p ≠ d := by
    intro hpd
    have := hq.2.2.2.1
    omega
  have := h3.2 hpq hpd
  omega
end Formalism.FrobeniusOrbits.Mu
