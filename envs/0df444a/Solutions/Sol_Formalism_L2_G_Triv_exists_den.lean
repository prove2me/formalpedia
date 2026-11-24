-- Prove2me | solution 1 for Formalism.L2.G.Triv.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:32.207049+00:00
-- url     : https://prove2.me/submissions/ae9eb490-1fcb-4ab5-b2fb-ba02dd1331ea

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Theorems.Thm_Formalism_L2_G_Triv_T_int
import Theorems.Thm_Formalism_L2_G_Triv_expand
import Theorems.Thm_Formalism_UG_P_adelstabL_den
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.L2.G.Triv
theorem _root_.solution : ∃ d : ℤ, d ≠ 0 ∧ ∀ z : 𝒜, (∀ v, prV (E := E) v z ∈ SV E v) →
    inclE (F := F) 𝔸 (d : E) * z ∈ 𝒮 := by
  classical
  let β₀ := Module.finBasis F E
  obtain ⟨m₁, hm₁, hi₁⟩ := adelstabL_den (fun i => β₀ i)
  have hu : ∀ _ : Fin (Module.finrank F E), IsUnit ((m₁ : ℤ) : F) := fun _ => (Int.cast_ne_zero.2 hm₁).isUnit
  let β := β₀.isUnitSMul hu
  have hβ : ∀ i, IsIntegral ℤ (β i) := by
    intro i
    have : β i = (m₁ : E) * β₀ i := by
      rw [Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]
    rw [this]; exact hi₁ i
  obtain ⟨m₂, hm₂, hi₂⟩ := adelstabL_den (fun i => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i)
  refine ⟨m₂, hm₂, fun z hz => ?_⟩
  rw [expand β z, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  have ht : adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) ∈ intAd F := by
    refine T_int _ fun v => ?_
    rw [map_mul]
    refine mul_mem ?_ (hz v)
    exact Subring.subset_closure (Or.inl ⟨⟨β i, ⟨⟨β i, hβ i⟩, rfl⟩⟩, rfl⟩)
  have h1 : inclE (F := F) 𝔸 (m₂ : E) * ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i ⊗ₜ[F]
      adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z)) =
      algebraMap (𝓞 E) E ⟨_, hi₂ i⟩ ⊗ₜ[F] adelstabT F E ((β i ⊗ₜ[F] (1 : 𝔸)) * z) := by
    show ((m₂ : E) ⊗ₜ[F] (1 : 𝔸)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  rw [h1]
  exact levelaf_tmul_mem _ ht
end Formalism.L2.G.Triv
