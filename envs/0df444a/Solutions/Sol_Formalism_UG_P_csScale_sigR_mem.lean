-- Prove2me | solution 1 for Formalism.UG.P.csScale_sigR_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:30.160329+00:00
-- url     : https://prove2.me/submissions/d4c1a422-edb7-40ab-9575-1744d245e0fb

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Theorems.Thm_Formalism_UG_P_csScale_sigR_incl
import Theorems.Thm_Formalism_UG_P_csScale_sigma_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) {s : 𝒜} (hs : s ∈ 𝒮) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) s ∈ 𝒮 := by
  have key : 𝒮 ≤ Subring.comap (sigR σ (FiniteAdeleRing (𝓞 F) F)) 𝒮 := by
    apply Subring.closure_le.2
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hx
      have h1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (ιA (algebraMap (𝓞 E) E b)) =
          ιA (algebraMap (𝓞 E) E ⟨(σ : E →+* E) (algebraMap (𝓞 E) E b), csScale_sigma_int σ b⟩) :=
        csScale_sigR_incl σ _
      show sigR σ (FiniteAdeleRing (𝓞 F) F) (ιA (algebraMap (𝓞 E) E b)) ∈ 𝒮
      rw [h1]
      exact CS.incl_int _
    · have h2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        show Algebra.TensorProduct.map σ (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) ((1 : E) ⊗ₜ[F] y) = _
        rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) ∈ 𝒮
      rw [h2]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs
end Formalism.UG.P
