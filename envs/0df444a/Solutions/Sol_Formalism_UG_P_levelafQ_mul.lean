-- Prove2me | solution 1 for Formalism.UG.P.levelafQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:21.44241+00:00
-- url     : https://prove2.me/submissions/2bae924d-4ded-40f8-8e57-69884582cc33

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelafQ_sum
import Theorems.Thm_Formalism_UG_P_levelafQ_tmul

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
theorem _root_.solution {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : 𝒜} (hx : levelafQ b x) (hy : levelafQ b y) : levelafQ b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine levelafQ_sum b _ _ fun j _ => levelafQ_sum b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact levelafQ_tmul b hb _ (mul_mem (hr j) (hr' k))
end Formalism.UG.P
