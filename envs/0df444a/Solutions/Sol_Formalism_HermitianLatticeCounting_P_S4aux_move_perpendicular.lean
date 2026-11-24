-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.move_perpendicular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:56.990798+00:00
-- url     : https://prove2.me/submissions/40a3558c-9803-4152-ac77-475b7b459422

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_move_involutive
import Theorems.Thm_Formalism_SL_Final_eichInt
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
theorem _root_.solution : MovePerp := by
  intro E _ _ V _ _ h O abelian₂ th x x' u s hH hth hL hI hxx hx'x' hux hux' hs hT
  have hT' := hT
  obtain ⟨⟨w, hw, he⟩, hu, hsx, hssx, ⟨d, hd, hk⟩⟩ := hT
  obtain ⟨⟨⟨w1, hw1, he1⟩, hu1, hsx1, hssx1, _⟩, hL1, hI1, hback, _, _⟩ :=
    move_involutive E V h O abelian₂ th x x' u s hH hL hI hxx hux hux' hs hT'
  have inv' := Formalism.SL.Final.eichInv E V h x' u s hH hx'x' hux' hs
  have iso' := Formalism.SL.Final.eichIsom E V h x' u s hH hx'x' hux' hs
  have inv := Formalism.SL.Final.eichInv E V h x u s hH hxx hux hs
  have hx'u : h x' u = 0 := by rw [hH u x', hux', star_zero]
  have nx' : eich h x' u s x' = x' := by simp [eich, hx'u, hx'x']
  have hkO : h x' x ∈ O := by rw [hk]; exact O.mul_mem hth hd
  ext v
  constructor
  · rintro ⟨v0, ⟨hv0, hp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change eich h x u s (eich h x' u s v0) ∈ abelian₂
      exact Formalism.SL.Final.eichInt E V h O abelian₂ x x' u s hH hL hI hu (by rw [he]; exact hL th hth _ hw) hsx hkO hux hux' v0 hv0 hp
    · have e : h (eich h x' u s v0) x' = h (eich h x' u s v0) (eich h x' u s x') := by rw [nx']
      change h (eich h x' u s v0) x' = 0
      rw [e, iso']; exact hp
  · rintro ⟨hv, hp⟩
    refine ⟨eich h x' (-u) (star s) v, ⟨?_, ?_⟩, (inv' v).2⟩
    · have := Formalism.SL.Final.eichInt E V h O (moved h x u s abelian₂) x x' (-u) (star s) hH hL1 hI1 hu1
        (by rw [he1]; exact hL1 th hth _ hw1) hsx1 hkO (by simp [hux]) (by simp [hux']) v hv hp
      change eich h x u s (eich h x (-u) (star s) (eich h x' (-u) (star s) v)) ∈ abelian₂ at this
      rwa [(inv _).2] at this
    · have : h (eich h x' (-u) (star s) v) x' = h (eich h x' u s (eich h x' (-u) (star s) v)) (eich h x' u s x') := (iso' _ _).symm
      rw [this, (inv' v).2, nx']; exact hp
end Formalism.HermitianLatticeCounting.P.S4aux
