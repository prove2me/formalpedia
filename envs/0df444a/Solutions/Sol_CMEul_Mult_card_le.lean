-- Prove2me | solution 1 for CMEul.Mult.card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:45.265042+00:00
-- url     : https://prove2.me/submissions/62d24a2d-e7ba-44a5-8591-4e202606a635

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul CMEul.Mult
open Formalism.HermitianLatticesTheory
namespace CMEul.Mult
theorem _root_.solution {K : Type} [Field K] [NumberField K] (n : ℕ) (hn : 2 ≤ n)
    (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (hs : ∀ P ∈ s, Ideal.absNorm P.1 = n) :
    s.card ≤ Module.finrank ℤ (𝓞 K) := by
  classical
  have hdvd : ∏ P ∈ s, P.1 ∣ Ideal.span {algebraMap ℤ (𝓞 K) (n : ℤ)} := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro P _ Q _ hPQ
      exact Ideal.isCoprime_iff_sup_eq.mpr (P.2.coprime_of_ne Q.2 (fun h => hPQ (Subtype.ext h)))
    · intro P hP
      rw [Ideal.dvd_span_singleton]
      have hm := Ideal.absNorm_mem P.1
      rw [hs P hP] at hm
      simpa using hm
  have h2 := map_dvd Ideal.absNorm hdvd
  rw [map_prod, Ideal.absNorm_span_singleton, Algebra.norm_algebraMap] at h2
  have h3 : ∏ P ∈ s, Ideal.absNorm P.1 = n ^ s.card := by
    rw [Finset.prod_congr rfl hs, Finset.prod_const]
  rw [h3, Int.natAbs_pow, Int.natAbs_natCast] at h2
  exact (Nat.pow_dvd_pow_iff_le_right (by omega)).mp h2
end CMEul.Mult
