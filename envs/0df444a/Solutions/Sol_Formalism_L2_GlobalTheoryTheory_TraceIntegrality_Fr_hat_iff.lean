-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.hat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:23.904325+00:00
-- url     : https://prove2.me/submissions/6004a6ea-fb0b-4b67-a7b1-9b44d9d6764f

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_hat_fwd

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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
theorem _root_.solution (G : GL n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ')
    (u : n → 𝒜) : u ∈ hat F Λ ↔ ((G : Matrix n n E).map ιA) *ᵥ u ∈ hat F Λ' := by
  constructor
  · exact hat_fwd _ (fun x hx => (h x).1 hx) u
  · intro hu
    have h1 : ∀ x ∈ Λ', ((G⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ Λ := by
      intro x hx
      refine (h _).2 ?_
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact hx
    have h2 := hat_fwd _ h1 _ hu
    rwa [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec] at h2
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
