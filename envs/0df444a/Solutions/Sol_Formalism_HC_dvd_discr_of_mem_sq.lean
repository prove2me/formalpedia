-- Prove2me | solution 1 for Formalism.HC.dvd_discr_of_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:21.760334+00:00
-- url     : https://prove2.me/submissions/e836679d-9eda-49ea-bed5-d29bc7835d23

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
open Formalism Formalism.HC
namespace Formalism.HC
theorem _root_.solution (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → (p : 𝓞 E) ∈ P ^ 2) : (p : ℤ) ∣ discr E := by
  by_contra hd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  obtain ⟨P, hPm, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (span {(p : ℤ)})
  have hP := hPm.isPrime
  have hb : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hv : (p : 𝓞 E) ∈ P := by simpa using (Ideal.liesOver_span_iff hP.ne_top hpz).1 hlo
  have hun := (not_dvd_discr_iff_forall_mem E (𝓞 E) hpz).1 hd P hP (by simpa using hv)
  have hu : P.under ℤ = span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (P.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (P.under ℤ).ResidueField := inferInstance
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) = span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h P hP hv
end Formalism.HC
