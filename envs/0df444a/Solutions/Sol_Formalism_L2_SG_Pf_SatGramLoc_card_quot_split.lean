-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.card_quot_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:35.739092+00:00
-- url     : https://prove2.me/submissions/5239e23c-505a-456b-96e9-ec35c4abf759

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_liesOver_natCast
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_ram_inertia_split

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
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := liesOver_natCast p hp v hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
  have hf := (ram_inertia_split p hp hs v hv).2
  have h2 : (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal = 1 := by
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, hf]
  rw [h2, pow_one] at h
  rw [← h, Ideal.absNorm_apply, Submodule.cardQuot_apply]
end Formalism.L2.SG.Pf.SatGramLoc
