-- Prove2me | solution 1 for Formalism.UG.P.levelaf_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:06:47.012737+00:00
-- url     : https://prove2.me/submissions/a6bb35c9-64db-4e45-aa2f-c952b10748f5

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelafQ_zero
import Theorems.Thm_Formalism_UG_P_levelafQ_add
import Theorems.Thm_Formalism_UG_P_levelafQ_neg
import Theorems.Thm_Formalism_UG_P_levelafQ_tmul
import Theorems.Thm_Formalism_UG_P_levelafQ_mul

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
    {s : 𝒜} (hs : s ∈ 𝒮) : levelafQ b s := by
  refine Subring.closure_induction (p := fun s _ => levelafQ b s) ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact levelafQ_tmul b hb e' (one_mem _)
    · have := levelafQ_tmul b hb 1 hy
      rwa [map_one] at this
  · exact levelafQ_zero b
  · have := levelafQ_tmul b hb 1 (one_mem (intAd F))
    rwa [map_one, ← Algebra.TensorProduct.one_def] at this
  · intro x y _ _ hx hy; exact levelafQ_add b hx hy
  · intro x _ hx; exact levelafQ_neg b hx
  · intro x y _ _ hx hy; exact levelafQ_mul b hb hx hy
end Formalism.UG.P
