-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Principal.inertia_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:52.18644+00:00
-- url     : https://prove2.me/submissions/55281a32-dc5d-4dfc-adfd-2743ac083d09

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
import Theorems.Thm_Formalism_FrobeniusOrbits_Principal_galE_restrict_mem_Psi
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_FrobeniusOrbits_galE_eq_one_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostFrob_of
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalSpec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostInertia
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd
import Theorems.Thm_P2M_Formalism_FrobeniusOrbits_Inertia_neg_one_ne_one__f153e1d875d4
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Principal
theorem _root_.solution (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hP0 : P ≠ ⊥)
    (h2 : ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∉ P) (hq : ((q : ℤ) : 𝓞 (hostE ζ a b)) ∉ P)
    (σ : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) : σ = 1 := by
  have hqd := hH.toHypOdd
  set σ' : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b := σ.restrictScalars ℚ with hσ'
  have hin : ∀ x : 𝓞 (hostE ζ a b), σ' • x - x ∈ P := hσ
  suffices hs : σ' = 1 from AlgEquiv.ext fun x => DFunLike.congr_fun hs x
  obtain ⟨p, hp, hPp⟩ :=
    (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)
  have hlo : P.LiesOver (span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hpmem : ((p : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact mem_span_singleton_self _
    simpa [Ideal.under_def] using this
  have hp2 : p ≠ 2 := by rintro rfl; exact h2 (by exact_mod_cast hpmem)
  have hpq : p ≠ q := by rintro rfl; exact hq hpmem
  by_cases hpd : p = d
  · subst hpd
    rcases ((hostInertia e q p hH L ζ a b h σ').2.2 P).mp hin with h1 | h1
    · exact (galE_eq_one_iff hqd h σ').mp h1
    · exfalso
      have hm := galE_restrict_mem_Psi (e := e) σ
      rw [mem_Psi_iff] at hm
      rw [← hσ', h1] at hm
      exact Inertia.neg_one_ne_one' hm
  · have : Fact p.Prime := ⟨hp⟩
    exact ((hostFrob_of hostGalois hostGalSpec e q d hqd L ζ a b h p hp2 hpq hpd P).2.2 σ').mp hin
end Formalism.FrobeniusOrbits.Principal
