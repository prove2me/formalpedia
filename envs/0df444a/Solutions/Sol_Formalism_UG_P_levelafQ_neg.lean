-- Prove2me | solution 1 for Formalism.UG.P.levelafQ_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:02.545776+00:00
-- url     : https://prove2.me/submissions/5dc51cf3-91e7-42eb-a406-9e8b46cd98da

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution {m : ℕ} (b : Fin m → 𝓞 E) {x : 𝒜} (hx : levelafQ b x) :
    levelafQ b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨-r, fun j => neg_mem (hr j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_neg _ _).symm
end Formalism.UG.P
