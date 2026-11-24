-- Prove2me | solution 1 for Formalism.SLP.P.CountO.exists_local_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:27.988779+00:00
-- url     : https://prove2.me/submissions/684cd89d-c07f-42a1-9e12-0d8cf8d9abe3

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) {ι : Type} (t : Finset ι)
    (c : ι → R) (hc : ∃ i ∈ t, c i ≠ 0) :
    ∃ i0 ∈ t, c i0 ≠ 0 ∧ ∃ s : R, s ∉ P ∧ ∃ d : ι → R, ∀ i ∈ t, s * c i = c i0 * d i := by
  classical
  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  let f : ι → ℕ∞ := fun i => IsDiscreteValuationRing.addVal Rp (algebraMap R Rp (c i))
  obtain ⟨j, hj, hjc⟩ := hc
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image t f ⟨j, hj⟩
  have hi0ne : c i0 ≠ 0 := by
    intro h0
    have h1 : f i0 = ⊤ := by simp [f, h0]
    have h2 : f j ≠ ⊤ := by
      simp only [f, ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
      exact (map_ne_zero_iff _ hinj).mpr hjc
    exact h2 (top_le_iff.mp (h1 ▸ hmin j hj))
  have hdvd : ∀ i ∈ t, algebraMap R Rp (c i0) ∣ algebraMap R Rp (c i) := fun i hi =>
    (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hmin i hi)
  choose! w hw using hdvd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples P.primeCompl t w
  have hb' : ∀ i ∈ t, ∃ r : R, algebraMap R Rp r = (b : R) • w i :=
    fun i hi => RingHom.mem_rangeS.mp (hb i hi)
  choose! d hd using hb'
  refine ⟨i0, hi0, hi0ne, (b : R), b.2, d, fun i hi => ?_⟩
  apply hinj
  rw [map_mul, map_mul, hd i hi, hw i hi, Algebra.smul_def]
  ring
end Formalism.SLP.P.CountO
