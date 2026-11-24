-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.moveAdm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:24.912913+00:00
-- url     : https://prove2.me/submissions/788cd85d-6d4d-4fa3-b53b-7d96571d2015

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_eich_sub
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_eich_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H1 : MoveCong) (H2 : EichInv) : MoveAdm := by
  intro E _ _ V _ _ h O abelian₂ th x x' u f f' s hh hth hL hI hu hsx hb hxx' hx hux hux' hs hf' hf'x' hff'
  have inv := H2 E V h x u s hh hx hux hs
  have e1 : eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f)
        = eich h x u s (eich h x' u s f') - f := by
    rw [eich_sub, (inv f).2]
  have c := (H1 E V h O abelian₂ th x x' u s hh hth hL hI hu hsx hb hxx' hux hux' f' hf' hf'x').2.2.2
  have e2 : InTh th abelian₂ (eich h x u s (eich h x' u s f') - f) := by
    have := inTh_add c hff'
    convert this using 1; abel
  refine ⟨e1, e2, ?_⟩
  obtain ⟨w₀, hw₀, ew⟩ := e2
  refine ⟨eich h x (-u) (star s) w₀, ?_, ?_⟩
  · show eich h x u s (eich h x (-u) (star s) w₀) ∈ abelian₂
    rw [(inv w₀).2]; exact hw₀
  · have : eich h x (-u) (star s) (eich h x u s (eich h x' u s f' - eich h x (-u) (star s) f))
        = eich h x (-u) (star s) (th • w₀) := by rw [e1, ew]
    rw [(inv _).1, eich_smul] at this
    exact this
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
