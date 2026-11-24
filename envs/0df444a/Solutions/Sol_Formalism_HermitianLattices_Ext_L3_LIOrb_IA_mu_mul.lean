-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.IA.mu_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:51.9863+00:00
-- url     : https://prove2.me/submissions/33ec04c9-a3a1-40fc-9f0f-3858f1d1eab2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_sSup_le_pow


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.IA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.IA
theorem _root_.solution {𝔮 : Ideal (𝓞 F)} (h𝔮 : 𝔮.IsMaximal) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) : mu 𝔮 (I * J) = mu 𝔮 I + mu 𝔮 J := by
  let v := BrA.maxEquiv F ⟨𝔮, h𝔮⟩
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  have e : ∀ X : Ideal (𝓞 F), X ≠ ⊥ → mu 𝔮 X = multiplicity v.asIdeal X :=
    fun X hX => BrA.sSup_le_pow v hX
  rw [e _ hIJ, e _ hI, e _ hJ]
  exact multiplicity_mul v.prime (FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hIJ)
end Formalism.HermitianLattices.Ext.L3.LIOrb.IA
