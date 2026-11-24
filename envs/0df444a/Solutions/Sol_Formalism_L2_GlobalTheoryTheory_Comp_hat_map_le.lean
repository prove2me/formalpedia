-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.Comp.hat_map_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:02:20.413331+00:00
-- url     : https://prove2.me/submissions/2a3f7206-2ed5-434d-9647-bb4f8d860e71

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob

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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.Comp
theorem _root_.solution (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜) (hu : u ∈ hat F Λ) :
    (Q.map ιA) *ᵥ u ∈ hat F (mapQ Q Λ) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨Q *ᵥ y, ⟨y, hy, rfl⟩, ?_⟩
    funext i
    exact RingHom.map_mulVec ιA Q y i
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    rw [Subring.smul_def, mulVec_smul]
    exact Submodule.smul_mem _ s hu
end Formalism.L2.GlobalTheoryTheory.Comp
