-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LHost.recMap_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:30:51.051802+00:00
-- url     : https://prove2.me/submissions/03a5dd67-7a1c-431e-963e-38854df380b0

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_unitsMap_eq_unitOfCoprime_iff
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_sgn2_toAdd_eq_ite
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_legU_of_modEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)
namespace Formalism.LFunctionChainParameters.LHost
theorem _root_.solution {e q d : ℕ} [Fact q.Prime] [Fact d.Prime] [NeZero (hostN e q d)] (u : (ZMod (hostN e q d))ˣ)
    (kd kq k2 : ℕ) (hk2 : k2.Coprime (2 ^ (e + 2)))
    (h1 : (u : ZMod (hostN e q d)).val ≡ kd [MOD d]) (h2 : (u : ZMod (hostN e q d)).val ≡ kq [MOD q])
    (h3 : (u : ZMod (hostN e q d)).val ≡ k2 [MOD 2 ^ (e + 2)]) :
    Multiplicative.toAdd (recMap e q d u)
      = ((if jacobiSym (kd : ℤ) d = 1 then 0 else 1, if jacobiSym (kq : ℤ) q = 1 then 0 else 1),
        Additive.ofMul (hcl e (ZMod.unitOfCoprime k2 hk2))) := by
  change ((Multiplicative.toAdd (sgn2 (legU _ d (d_dvd_hostN e q d) u)),
      Multiplicative.toAdd (sgn2 (legU _ q (q_dvd_hostN e q d) u))),
      Additive.ofMul (hcl e (ZMod.unitsMap (two_dvd_hostN e q d) u))) = _
  rw [sgn2_toAdd_eq_ite, sgn2_toAdd_eq_ite, legU_of_modEq _ u kd h1, legU_of_modEq _ u kq h2,
    (unitsMap_eq_unitOfCoprime_iff _ hk2 u).2 h3]
end Formalism.LFunctionChainParameters.LHost
