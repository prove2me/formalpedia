-- Prove2me | solution 1 for CriticalPortraits.beta_unlinked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:37:56.774495+00:00
-- url     : https://prove2.me/submissions/4d43589f-2186-4642-8d2f-1ff9ed52371c

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
public import Theorems.Thm_CriticalPortraits_mem_beta_iff
public import Theorems.Thm_CriticalPortraits_betaBlock_disjoint
public import Theorems.Thm_CriticalPortraits_beta_interval_closed
public import Theorems.Thm_CriticalPortraits_maxVal_ge
public import Theorems.Thm_CriticalPortraits_minVal_le


set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) :
    ∀ A ∈ beta U, ∀ B ∈ beta U, A ≠ B → Unlinked A B := by
  have : NeZero (d*m) := ⟨by positivity⟩
  intro A hA B hB hAB
  rw [mem_beta_iff] at hA hB
  obtain ⟨x, hx, hAx⟩ := hA
  obtain ⟨z, hz, hBz⟩ := hB
  subst hAx; subst hBz
  intro hL
  -- destructure the crossing quadruple
  obtain ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, hcase⟩ := hL
  -- both cases are symmetric; reduce to a1<b1<a2<b2 form by relabelling
  -- nonempty witnesses
  have hAne := betaBlock_nonempty hx
  have hBne := betaBlock_nonempty hz
  -- helper: a "linked" quadruple across two distinct blocks forces equal blocks (contradiction).
  -- symmetric in the two block-vertices.
  have core : ∀ s t : ZMod (d*m), s ∈ bVerts U → t ∈ bVerts U →
      betaBlock U s ≠ betaBlock U t →
      ∀ p1 p2 q1 q2 : ZMod (d*m),
      p1 ∈ betaBlock U s → p2 ∈ betaBlock U s → q1 ∈ betaBlock U t → q2 ∈ betaBlock U t →
      p1.val < q1.val → q1.val < p2.val → p2.val < q2.val → False := by
    intro s t hs ht hst p1 p2 q1 q2 hp1 hp2 hq1 hq2 ho1 ho2 ho3
    have hSne := betaBlock_nonempty hs
    have hTne := betaBlock_nonempty ht
    -- q1 strictly inside S's span
    have hminS_le_p1 : (minVal (betaBlock U s) hSne).val ≤ p1.val := minVal_le _ hSne _ hp1
    have hp2_le_maxS : p2.val ≤ (maxVal (betaBlock U s) hSne).val := maxVal_ge _ hSne _ hp2
    have hq1_loS : (minVal (betaBlock U s) hSne).val < q1.val := by omega
    have hq1_hiS : q1.val < (maxVal (betaBlock U s) hSne).val := by omega
    -- T ⊆ [minS, maxS]
    have hTin := beta_interval_closed hd hm hcanon hs ht hst hq1 hq1_loS hq1_hiS
    -- p2 strictly inside T's span
    have hminT_le_q1 : (minVal (betaBlock U t) hTne).val ≤ q1.val := minVal_le _ hTne _ hq1
    have hq2_le_maxT : q2.val ≤ (maxVal (betaBlock U t) hTne).val := maxVal_ge _ hTne _ hq2
    have hp2_loT : (minVal (betaBlock U t) hTne).val < p2.val := by omega
    have hp2_hiT : p2.val < (maxVal (betaBlock U t) hTne).val := by omega
    -- S ⊆ [minT, maxT]
    have hSin := beta_interval_closed hd hm hcanon ht hs (Ne.symm hst) hp2 hp2_loT hp2_hiT
    have hmS_mem : minVal (betaBlock U s) hSne ∈ betaBlock U s := minVal_mem _ hSne
    have hmT_mem : minVal (betaBlock U t) hTne ∈ betaBlock U t := minVal_mem _ hTne
    -- T ⊆ [minS,maxS] ⇒ minS ≤ minT; S ⊆ [minT,maxT] ⇒ minT ≤ minS
    have h1 : (minVal (betaBlock U s) hSne).val ≤ (minVal (betaBlock U t) hTne).val :=
      (hTin _ hmT_mem).1
    have h2 : (minVal (betaBlock U t) hTne).val ≤ (minVal (betaBlock U s) hSne).val :=
      (hSin _ hmS_mem).1
    have hmineq : (minVal (betaBlock U s) hSne).val = (minVal (betaBlock U t) hTne).val := by omega
    have hmineq' : minVal (betaBlock U s) hSne = minVal (betaBlock U t) hTne :=
      ZMod.val_injective _ hmineq
    have hdisj := betaBlock_disjoint hst
    have hmS_in_T : minVal (betaBlock U s) hSne ∈ betaBlock U t := by rw [hmineq']; exact hmT_mem
    exact (Finset.disjoint_left.mp hdisj hmS_mem) hmS_in_T
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact core x z hx hz hAB a1 a2 b1 b2 ha1 ha2 hb1 hb2 h1 h2 h3
  · exact core z x hz hx (Ne.symm hAB) b1 b2 a1 a2 hb1 hb2 ha1 ha2 h1 h2 h3
end CriticalPortraits
