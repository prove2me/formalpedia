-- Prove2me | solution 1 for Formalism.UG.P.cartan_val_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:13.313002+00:00
-- url     : https://prove2.me/submissions/c8d47933-31ee-4c15-ac67-db4d2aa813ad

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open IsDedekindDomain NumberField
namespace Formalism.UG.P
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) (x : v.adicCompletion F) (hx : x ≠ 0) :
    ∃ k : ℤ, Valued.v x = Valued.v ϖ ^ k := by
  unfold IsUnifV at h
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hx0
  refine ⟨-(Multiplicative.toAdd g), ?_⟩
  rw [h, ← hg, ← WithZero.coe_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp
end Formalism.UG.P
