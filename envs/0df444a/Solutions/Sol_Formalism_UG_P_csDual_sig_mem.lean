-- Prove2me | solution 1 for Formalism.UG.P.csDual_sig_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:42.16968+00:00
-- url     : https://prove2.me/submissions/a4b9a4cf-6a67-4a84-a50f-a62f9eef246f

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual

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
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) {s : 𝒜} (hs : s ∈ 𝒮) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) s ∈ 𝒮 := by
  have key : ∀ s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F),
      s ∈ (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)).comap
        (sigR σ (FiniteAdeleRing (𝓞 F) F)) := by
    intro s hs'
    refine (Subring.closure_le.2 ?_) hs'
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨a, ha⟩ := hx
      have hint : IsIntegral ℤ (σ x) := by
        rw [← ha]
        simpa using (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := ℤ) a)).map
          σ.toRingHom.toIntAlgHom
      have e1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (x ⊗ₜ[F] (1 : (FiniteAdeleRing (𝓞 F) F))) = (σ x) ⊗ₜ[F] (1 : (FiniteAdeleRing (𝓞 F) F)) := by
        simp [sigR]
      show sigR σ (FiniteAdeleRing (𝓞 F) F) (x ⊗ₜ[F] (1 : (FiniteAdeleRing (𝓞 F) F))) ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
      rw [e1]
      exact Subring.subset_closure (Or.inl ⟨⟨σ x, IsIntegralClosure.mk' (𝓞 E) _ hint,
        IsIntegralClosure.algebraMap_mk' _ _ _⟩, rfl⟩)
    · have e2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        simp [sigR]
      show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
      rw [e2]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key s hs
end Formalism.UG.P
