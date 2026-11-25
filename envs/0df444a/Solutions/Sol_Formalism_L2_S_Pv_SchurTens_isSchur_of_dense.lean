-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.isSchur_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:24:34.463887+00:00
-- url     : https://prove2.me/submissions/ee939276-41fa-4c62-8992-8074dafefa51

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_memLp_of_diag
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_of_dense_a
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_of_dense_b
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (hSp : ∀ a ∈ Sp, ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, SP m σs D a b a' b') :
    IsSchur m σs D := by

  have h1 : ∀ b ∈ Sp, ∀ a' ∈ Sp, ∀ b' ∈ Sp, ∀ a : Hs,
      SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
    intro b hb a' ha' b' hb' a
    exact SP_of_dense_a hstr hD Sp hdense b a' b' (fun a₀ h₀ => hSp a₀ h₀ b hb a' ha' b' hb')
      (fun c hc => hSp c hc b hb c hc b hb)
      (memLp_of_diag hstr (hSp a' ha' b' hb' a' ha' b' hb')) a

  have h2 : ∀ b ∈ Sp, ∀ b' ∈ Sp, ∀ a a' : Hs, SP m σs D a b a' b' := by
    intro b hb b' hb' a a'
    have h := SP_of_dense_a hstr hD Sp hdense b' a b
      (fun a₀ h₀ => SP_swap (h1 b hb a₀ h₀ b' hb' a).1)
      (fun c hc => hSp c hc b' hb' c hc b' hb')
      (h1 b hb b' hb' b' hb' a).2 a'
    exact SP_swap h.1

  have h3 : ∀ b' ∈ Sp, ∀ a a' b : Hs, SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by
    intro b' hb' a a' b
    exact SP_of_dense_b hstr hD Sp hdense a a' b'
      (fun b₀ h₀ => h2 b₀ h₀ b' hb' a a')
      (fun c hc => h2 c hc c hc a a)
      (h1 b' hb' b' hb' b' hb' a').2 b

  refine ⟨hD, fun a b a' b' => ?_⟩
  have h4 := SP_of_dense_b hstr hD Sp hdense a' a b
    (fun b₀ h₀ => SP_swap (h3 b₀ h₀ a a' b).1)
    (fun c hc => h2 c hc c hc a' a')
    (h3 0 Sp.zero_mem a a b).2 b'
  exact SP_swap h4.1
end Formalism.L2.S.Pv.SchurTens
