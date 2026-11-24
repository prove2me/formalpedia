-- Prove2me | solution 1 for Formalism.L2.DIV.valuation_eq_one_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:23.129608+00:00
-- url     : https://prove2.me/submissions/f3e8e535-150e-4093-9217-fe33a8655a32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.DIV
theorem _root_.solution (k : F) (hk : k ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      Valued.v (algebraMap F (v.adicCompletion F) k) = 1 := by
  have h1 := (algebraMap F 𝔸 k).2
  have h2 := (algebraMap F 𝔸 k⁻¹).2
  filter_upwards [h1, h2] with v a b
  have a' : Valued.v (algebraMap F (v.adicCompletion F) k) ≤ 1 := a
  have b' : Valued.v (algebraMap F (v.adicCompletion F) k⁻¹) ≤ 1 := b
  rw [map_inv₀, map_inv₀] at b'
  have hpos : 0 < Valued.v (algebraMap F (v.adicCompletion F) k) :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hk))
  exact le_antisymm a' ((inv_le_one₀ hpos).mp b')
end Formalism.L2.DIV
