-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.summable_inv_absNorm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:36.651616+00:00
-- url     : https://prove2.me/submissions/0436e897-511c-40d9-b560-a9705890fd8c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_le_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_prime
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_summable_resChar_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution :
    Summable fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => ((Ideal.absNorm 𝔭.1 : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun 𝔭 => by positivity) (fun 𝔭 => ?_)
    (IdealNormInequalities.summable_resChar_sq (K := F))
  have h1 : (0 : ℝ) < (IdealNormInequalities.resChar 𝔭.1 : ℝ) := by
    exact_mod_cast (IdealNormInequalities.resChar_prime 𝔭.2).pos
  have h2 : (IdealNormInequalities.resChar 𝔭.1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    exact_mod_cast IdealNormInequalities.resChar_le_absNorm 𝔭.2
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h1.le h2 2)
end Formalism.HermitianLattices.Ext.L3.A5
