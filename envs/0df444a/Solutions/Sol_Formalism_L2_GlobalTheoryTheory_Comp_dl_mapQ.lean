-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.dl_mapQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:11.79626+00:00
-- url     : https://prove2.me/submissions/b4dad7ad-a5f6-4e5a-8bfd-7759f7e1d2e4

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ExistsUnitaryOneDetEq
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_mulVec_rect
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1)
    (hQ : cT (σ : E →+* E) Q * (1 : Matrix m m E) * Q = J) (M : Submodule (𝓞 E) (n → E)) :
    dl σ (1 : Matrix m m E) (mapQ Q M) = mapQ Q (dl σ J M) := by
  have key : ∀ a b, hform (σ : E →+* E) (1 : Matrix m m E) (Q *ᵥ a) (Q *ᵥ b) = hform (σ : E →+* E) J a b := by
    intro a b
    rw [hform_mulVec_rect, hQ]
  unfold dl mapQ
  rw [Submodule.map_span]
  congr 1
  ext x
  unfold dualSet
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨Q' *ᵥ x, ?_, ?_⟩
    · intro y hy
      have h := hx (Q *ᵥ y) ⟨y, hy, rfl⟩
      rw [← key y (Q' *ᵥ x), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      exact h
    · show Q *ᵥ (Q' *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rintro ⟨z, hz, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    show hform _ 1 (Q *ᵥ y) (Q *ᵥ z) ∈ _
    rw [key]
    exact hz y hy
end Formalism.L2.GlobalTheoryTheory.Comp
