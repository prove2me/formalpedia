-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.realize_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:56.233923+00:00
-- url     : https://prove2.me/submissions/3c6fbc3a-75dc-4f57-8e6f-cb76457b4585

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    Formalism.HermitianLatticesTheory.realize b X x p =
      if p.2.2 = 0 then (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).re else (Formalism.HermitianLatticesTheory.fcoord b X p.1 x p.2.1).im := by
  first
    | rfl
    | simp [Formalism.HermitianLatticesTheory.realize]
    | (unfold Formalism.HermitianLatticesTheory.realize; done)
end Formalism.HN.PlaceDecomposition
