-- Prove2me | solution 1 for Formalism.REAL.CharId_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:03.706516+00:00
-- url     : https://prove2.me/submissions/90245aa4-27ee-406f-8e9e-f4daf454d5f4

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_aeval_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (v : V) (j : ℕ) (q : ℂ[X])
    (hgen : ∀ t : Fin n, j ≤ (t : ℕ) → aeval (CharId_M E) q (Pi.single t v) = 0) :
    ∀ y ∈ CharId_F E v j, aeval (CharId_M E) q y = 0 := by
  intro y hy
  have hW : LinearMap.ker (aeval (CharId_M E) q) ∈ {W : Submodule ℂ (Fin n → V) |
      (∀ t : Fin n, j ≤ (t : ℕ) → Pi.single t v ∈ W) ∧ ∀ c d, ∀ y ∈ W, twistedAction E c d y ∈ W} := by
    refine ⟨fun t ht => LinearMap.mem_ker.2 (hgen t ht), fun c d z hz => ?_⟩
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← Module.End.mul_apply, ← CharId_aeval_comm E hE q c d, Module.End.mul_apply, hz, map_zero]
  exact LinearMap.mem_ker.1 (Submodule.mem_sInf.1 hy _ hW)
end Formalism.REAL
