-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.place_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:28.910436+00:00
-- url     : https://prove2.me/submissions/ddb35304-56fe-43ed-b96c-8e7ba75f4147

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanSingletonEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {x : V} (hx : x ≠ 0) (w : InfinitePlace K) :
    w (h x x) = (w.embedding (h x x)).re := by
  have h1 : star (h x x) = h x x := hs.eq x x
  have h2 : (w.embedding (h x x)).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← hK.2.1, h1]
  rw [← InfinitePlace.norm_embedding_eq, ← Complex.abs_re_eq_norm.2 h2,
    abs_of_pos (hd x hx w.embedding)]
end Formalism.HermitianLattices.Ext.L3.BallB
