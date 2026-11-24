-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.splitDiff_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:44.017928+00:00
-- url     : https://prove2.me/submissions/8840fc20-d09e-4155-9017-cbdaacf2cad2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution : SplitDiff := by
  intro F E _ _ _ _ _ p P hp hPm hpP hpP2 h
  haveI : P.IsPrime := hPm.isPrime
  have hDE : differentIdeal ℤ (𝓞 E) ≤ P := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]
    exact le_trans Ideal.mul_le_right h
  have hdvd : P ∣ differentIdeal ℤ (𝓞 E) := Ideal.dvd_iff_le.mpr hDE
  rw [dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain] at hdvd
  apply hdvd
  have hpu : ((p : ℤ)) ∈ P.under ℤ := by
    show (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
    rw [Ideal.mem_comap]
    simpa using hpP
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpu
    exact hp.ne_zero (by exact_mod_cast hpu)
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (P.under ℤ) P hne]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]
    exact Ideal.map_comap_le
  · intro hle
    have h2 := hle (Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 E)) hpu)
    apply hpP2
    simpa using h2
end Formalism.L2.SG.Pf.LatEx
