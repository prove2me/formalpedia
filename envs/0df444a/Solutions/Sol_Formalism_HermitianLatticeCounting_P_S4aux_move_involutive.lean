-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.move_involutive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:41.399558+00:00
-- url     : https://prove2.me/submissions/a29e1dda-3054-4f06-bb8b-8634bc834758

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_Final_eichInv
import Theorems.Thm_Formalism_SL_Final_eichIsom
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : MoveInvol := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s hH hL hI hxx hux hux' hs ⟨⟨w, hw, he⟩, hu, hsx, hssx, ⟨d, hd, hk⟩⟩
  have inv := Formalism.SL.Final.eichInv E V h x u s hH hxx hux hs
  have iso := Formalism.SL.Final.eichIsom E V h x u s hH hxx hux hs
  have hxu : h x u = 0 := by rw [hH u x, hux, star_zero]
  have hx'u : h x' u = 0 := by rw [hH u x', hux', star_zero]
  have nx : eich h x u s x = x := by simp [eich, hxu, hxx]
  have nb : eich h x u s (x + x') = th • (w - d • (u + s • x)) := by
    simp only [eich, map_add, LinearMap.add_apply, hxu, hxx, hx'u, hk]
    rw [he]; module
  have mem : ∀ v, v ∈ moved h x u s abelian₂ ↔ eich h x u s v ∈ abelian₂ := fun v => Iff.rfl
  have lin : ∀ (c : E) v, eich h x u s (c • v) = c • eich h x u s v := fun c v => (eichLin h x u s).map_smul c v
  have lin' : ∀ (c : E) v, eich h x (-u) (star s) (c • v) = c • eich h x (-u) (star s) v :=
    fun c v => (eichLin h x (-u) (star s)).map_smul c v
  refine ⟨⟨⟨eich h x (-u) (star s) (w - d • (u + s • x)), ?_, ?_⟩, ?_, ?_, ?_, ⟨d, hd, hk⟩⟩, ?_, ?_, ?_, neg_neg u, star_star s⟩
  · rw [mem, (inv _).2]; exact abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hsx))
  · rw [← lin', ← nb, (inv _).1]
  · rw [mem]
    have : eich h x u s (-u) = -(u + (s • x + star s • x)) := by
      simp only [eich, map_neg, LinearMap.neg_apply, hux, ← hs]; module
    rw [this]; exact abelian₂.neg_mem (abelian₂.add_mem hu (abelian₂.add_mem hsx hssx))
  · rw [mem, lin, nx]; exact hssx
  · rw [mem, lin, nx, star_star]; exact hsx
  · intro a ha v hv; rw [mem] at hv ⊢; rw [lin]; exact hL a ha _ hv
  · intro v hv v' hv'; rw [← iso v v']; exact hI _ hv _ hv'
  · ext v
    change eich h x u s (eich h x (-u) (star s) v) ∈ abelian₂ ↔ v ∈ abelian₂
    rw [(inv v).2]
end Formalism.HermitianLatticeCounting.P.S4aux
