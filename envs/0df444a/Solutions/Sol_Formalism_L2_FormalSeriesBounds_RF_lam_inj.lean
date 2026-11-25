-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.lam_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:53.847272+00:00
-- url     : https://prove2.me/submissions/4c628977-08ed-40e7-83d3-6b4dbfd25624

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod 2 → T)
  (gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
variable {r tau}
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by
  rintro ⟨⟨ρ, ⟨o, ⟨t, i⟩⟩⟩, col⟩ ⟨⟨ρ', ⟨o', ⟨t', i'⟩⟩⟩, col'⟩ h
  simp only [lam, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := inj (a₁ := (o, t)) (a₂ := (o', t')) h1
  simp only [Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have h4 := eq_of_heq h2
  simp only [Prod.mk.injEq] at h4
  obtain ⟨rfl, h5⟩ := h4
  have h6 := plc.injective h5
  simp only [Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  rfl
end Formalism.L2.FormalSeriesBounds.RF
