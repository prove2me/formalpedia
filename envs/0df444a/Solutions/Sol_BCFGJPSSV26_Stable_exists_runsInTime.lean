-- Prove2me | solution 1 for BCFGJPSSV26.Stable.exists_runsInTime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:06:17.512515+00:00
-- url     : https://prove2.me/submissions/ff32c9ca-aa18-4800-bbc4-b0445d058dc0

module

public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCore
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy
public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Constructible
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import all Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
public import Theorems.Thm_BCFGJPSSV26_Stable_exists_accN_inO
public import Theorems.Thm_BCFGJPSSV26_Stable_exists_algN_inO

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- **The running time**: `O(stableTimeOf a 2 + |(x, r)|)` for one `a`, and the budget is at most
`stableTimeOf a 2`. -/
theorem exists_runsInTime : ∃ a : ℕ, RunsInTime encILQ encCenters algQ (stableTimeOf a 2) ∧
    ∀ x : (Instance × ℕ) × ℚ, Par.budget (accN x.2) x.1.1 x.1.2 ≤ stableTimeOf a 2 x := by
  obtain ⟨d, hU⟩ := exists_algN_inO
  obtain ⟨D₀, hacc⟩ := exists_accN_inO
  set d' := d + D₀ + 1 with hd'
  refine ⟨d' * (10 ^ 6 * 2 ^ 16 + 1), ?_, fun x ↦ ?_⟩
  swap
  · refine le_trans ?_ (stableTime_le_stableTimeOf d' x)
    exact stableTime_mono (by nlinarith) _
  set X := fun x : ((Instance × ℕ) × ℚ) × List Bool ↦ (encPair encILQ encBits x).length with hX
  have hx1 := ComputableInO.fst encILQ encBits
  have hIL := (ComputableInO.fst (encPair encInstance encUnary) encRat).comp_linear hx1
  have hε := (ComputableInO.snd (encPair encInstance encUnary) encRat).comp_linear hx1
  have hNof := hacc.comp' hε
  have hr := ComputableInO.snd encILQ encBits
  have hg := (hIL.prod hNof).prod hr
  have hall := hU.comp' hg
  have hb : ∀ x : ((Instance × ℕ) × ℚ) × List Bool,
      X x + (X x + ((encRat x.1.2).length + accN x.1.2 ^ D₀)) + X x +
        (stableTime (d * Par.e₁ (accN x.1.2) + d) x.1.1 +
          (encILNr ((x.1.1, accN x.1.2), x.2)).length) ≤
      5 * (stableTimeOf (d' * (10 ^ 6 * 2 ^ 16 + 1)) 2 x.1 + X x + 1) := by
    intro x
    obtain ⟨⟨⟨I, L⟩, ε⟩, r⟩ := x
    set N := accN ε
    set ST := stableTimeOf (d' * (10 ^ 6 * 2 ^ 16 + 1)) 2 ((I, L), ε)
    have hle : ∀ {e}, e ≤ d' * Par.e₁ N + d' → stableTime e (I, L) ≤ ST := fun h ↦
      (stableTime_mono h _).trans (stableTime_le_stableTimeOf d' ((I, L), ε))
    have h1 : stableTime (d * Par.e₁ N + d) (I, L) ≤ ST := hle (by nlinarith)
    have h2 : N ^ D₀ ≤ ST := (pow_le_stableTime N D₀ (I, L)).trans (hle (by nlinarith))
    have h3 : N ≤ ST := by
      have := (pow_le_stableTime N 1 (I, L)).trans (hle (by nlinarith))
      rwa [pow_one] at this
    simp only [X, encILNr, encILN, encILQ, length_encPair, encUnary_apply,
      List.length_replicate]
    omega
  obtain ⟨c, hc, -⟩ := hall.mono 5 hb hb
  exact ⟨c, hc⟩

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.exists_runsInTime := @BCFGJPSSV26.Stable.exists_runsInTime
