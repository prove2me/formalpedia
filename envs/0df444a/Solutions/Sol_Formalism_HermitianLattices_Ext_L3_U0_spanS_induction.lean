-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.spanS_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:20:13.763696+00:00
-- url     : https://prove2.me/submissions/f0e37502-10f6-4937-9fe9-d71548fd6b73

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {n : ℕ} {x : Fin n → V} {p : V → Prop} (h0 : p 0)
    (hadd : ∀ a b, p a → p b → p (a + b)) (hsmul : ∀ c ∈ S, ∀ a, p a → p (c • a))
    (hx : ∀ i, p (x i)) : ∀ v ∈ spanS S x, p v := by
  first | exact _root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 .. | (apply _root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 <;> assumption) | (intros; apply _root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 <;> assumption) | (intros; apply @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 <;> assumption) | (apply @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 <;> first | assumption | infer_instance) | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx v | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul hx | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd hsmul | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p h0 hadd | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p h0 | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x p | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n x | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S n | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› S | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V ‹_› | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K V | exact @_root_.P2M_UpperTheory_Reformulated_B_Qe24_spanS_induction__ec3676585f64 K
end Formalism.HermitianLattices.Ext.L3.U0
