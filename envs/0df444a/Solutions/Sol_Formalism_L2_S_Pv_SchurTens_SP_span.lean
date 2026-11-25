-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.SP_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:24:10.726111+00:00
-- url     : https://prove2.me/submissions/0279557f-da76-4880-96c7-74f1bf7a23b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_swap
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_zero_a
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_add_a
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_smul_a
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_zero_b
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_add_b
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_smul_b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
section Gen
variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
private theorem mem_span_of_closed_lemma {P : Hs → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x)) {E : Set Hs} (hE : ∀ a ∈ E, P a) :
    ∀ a ∈ Submodule.span ℂ E, P a := by
  intro a ha
  let S : Submodule ℂ Hs :=
    { carrier := {x | P x}
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      zero_mem' := h0
      smul_mem' := fun c {x} hx => hsmul c x hx }
  have hle : Submodule.span ℂ E ≤ S := Submodule.span_le.mpr fun x hx => hE x hx
  exact hle ha
end Gen
section Pure
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}
end Pure
end Formalism.L2.S.Pv.SchurTens
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type*} [MeasurableSpace K] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution {E : Set Hs} (h : ∀ a ∈ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b') :
    ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ Submodule.span ℂ E,
      ∀ b' ∈ Submodule.span ℂ E, SP m σs D a b a' b' := by
  have s1 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b' :=
    mem_span_of_closed_lemma (P := fun a => ∀ b ∈ E, ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun b _ a' _ b' _ => SP_zero_a b a' b')
      (fun x y hx hy b hb a' ha' b' hb' => SP_add_a (hx b hb a' ha' b' hb') (hy b hb a' ha' b' hb'))
      (fun c x hx b hb a' ha' b' hb' => SP_smul_a c (hx b hb a' ha' b' hb'))
      (fun a ha => h a ha)
  have s2 : ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, ∀ a' ∈ E, ∀ b' ∈ E,
      SP m σs D a b a' b' := by
    intro a ha
    exact mem_span_of_closed_lemma (P := fun b => ∀ a' ∈ E, ∀ b' ∈ E, SP m σs D a b a' b')
      (fun a' _ b' _ => SP_zero_b a a' b')
      (fun x y hx hy a' ha' b' hb' => SP_add_b (hx a' ha' b' hb') (hy a' ha' b' hb'))
      (fun c x hx a' ha' b' hb' => SP_smul_b c (hx a' ha' b' hb'))
      (fun b hb => s1 a ha b hb)
  have s3 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E,
      SP m σs D a' b' a b :=
    mem_span_of_closed_lemma
      (P := fun a' => ∀ b' ∈ E, ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun b' _ a _ b _ => SP_zero_a b' a b)
      (fun x y hx hy b' hb' a ha b hb => SP_add_a (hx b' hb' a ha b hb) (hy b' hb' a ha b hb))
      (fun c x hx b' hb' a ha b hb => SP_smul_a c (hx b' hb' a ha b hb))
      (fun a' ha' b' hb' a ha b hb => SP_swap (s2 a ha b hb a' ha' b' hb'))
  have s4 : ∀ a' ∈ Submodule.span ℂ E, ∀ b' ∈ Submodule.span ℂ E, ∀ a ∈ Submodule.span ℂ E,
      ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b := by
    intro a' ha'
    exact mem_span_of_closed_lemma
      (P := fun b' => ∀ a ∈ Submodule.span ℂ E, ∀ b ∈ Submodule.span ℂ E, SP m σs D a' b' a b)
      (fun a _ b _ => SP_zero_b a' a b)
      (fun x y hx hy a ha b hb => SP_add_b (hx a ha b hb) (hy a ha b hb))
      (fun c x hx a ha b hb => SP_smul_b c (hx a ha b hb))
      (fun b' hb' => s3 a' ha' b' hb')
  intro a ha b hb a' ha' b' hb'
  exact SP_swap (s4 a' ha' b' hb' a ha b hb)
end Formalism.L2.S.Pv.SchurTens
