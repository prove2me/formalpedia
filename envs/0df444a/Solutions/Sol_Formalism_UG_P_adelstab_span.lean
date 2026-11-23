-- Prove2me | solution 1 for Formalism.UG.P.adelstab_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:04.471656+00:00
-- url     : https://prove2.me/submissions/447209e8-f658-4cd9-8a7e-003e5e9f1ca5

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_adelstab_mem_iff
import Theorems.Thm_Formalism_UG_P_levelafC_mul


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
theorem _root_.solution (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (c₁ d : 𝓞 F) (hc₁ : c₁ ≠ 0)
    (hd : d ≠ 0) (hL : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E c₁ * v i) ∈ L)
    (hG : ∀ i j, levelafC E d * ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j ∈ 𝒮) :
    Submodule.span E (adelstabLam F E G L : Set (n → E)) = ⊤ := by
  set u : E := algebraMap (𝓞 F) E (c₁ * d)
  have hu : u ≠ 0 := adelstab_algebraMap_ne_zero _ (mul_ne_zero hc₁ hd)
  have hk : ∀ k, Pi.single k u ∈ adelstabLam F E G L := by
    intro k
    rw [adelstab_mem_iff]
    have : (fun i => ι ((Pi.single k u : n → E) i)) = Pi.single k (ι u) := by
      ext i; by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [this, mulVec_single]
    convert hL (fun i => levelafC E d * ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i k) (fun i => hG i k)
      using 1
    ext i
    simp only [u, adelstab_incl_C, levelafC_mul, Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply]
    ring
  rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have : (Pi.basisFun E n) k = u⁻¹ • Pi.single k u := by
    rw [Pi.basisFun_apply, ← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hu]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hk k))
end Formalism.UG.P
