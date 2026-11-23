-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_dTop_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:57.767355+00:00
-- url     : https://prove2.me/submissions/a4380f11-aea1-4f4e-9145-3693f68736aa

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {d : ℕ} [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) (e : ℕ)
    (h : dTop d TT s = (e : ℕ∞)) : Odd e := by
  classical
  by_cases hne : ∃ e' : ℕ, Odd e' ∧ s + (e' : ZMod d) ∈ TT
  · have h1 : dTop d TT s = ((sInf {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT} : ℕ) : ℕ∞) := by
      rw [ENat.coe_sInf (s := {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT}) hne]
      rfl
    rw [h1] at h
    have hm := Nat.sInf_mem (s := {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT}) hne
    have he : sInf {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) ∈ TT} = e := by exact_mod_cast h
    rw [he] at hm
    exact hm.1
  · push_neg at hne
    have htop : dTop d TT s = ⊤ := by
      unfold dTop
      refine iInf_eq_top.mpr fun e' => iInf_eq_top.mpr fun h' => ?_
      exact absurd h'.2 (hne e' h'.1)
    rw [htop] at h
    exact absurd h (ENat.top_ne_coe e)
end Formalism.DworkPowerSeriesWeights
