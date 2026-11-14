-- Prove2me | solution 1 for BCFGJPSSV26.Stable.exists_algN_inO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:55.887389+00:00
-- url     : https://prove2.me/submissions/de0e1597-7c43-4621-94a2-6a088ee9595c

module

public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeCore
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Accuracy
public import Definitions.Def_BuhaiPapers_Background_BlackBox
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Constructible
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import all Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- **The running time with `N` as an input**: within `O(stableTime (d e₁ + d) (I, L) + |(y, r)|)`
on an input `y = ((I, L), N)` with coins `r`, for one `d` and all `N`. -/
theorem exists_algN_inO : ∃ d : ℕ, ComputableInO algN encILNr encCenters
    (fun xr ↦ stableTime (d * Par.e₁ xr.1.2 + d) xr.1.1 + (encILNr xr).length)
    (fun xr ↦ stableTime (d * Par.e₁ xr.1.2 + d) xr.1.1 + (encILNr xr).length) := by
  obtain ⟨D, hbud⟩ := exists_budget_inO
  obtain ⟨cC, dC, hCO⟩ := exists_inO_pow coinCnt_polytime
  obtain ⟨cR, dR, hRO⟩ := exists_inO_pow coreN_polytime
  obtain ⟨E, hE⟩ : ∃ E, E = D + dC + dR + 1 := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ((Instance × ℕ) × ℕ) × List Bool → ℕ,
      Φ = fun xr ↦ wt xr.1 ^ E + (encILNr xr).length := ⟨_, rfl⟩
  have hW1 : ∀ xr : ((Instance × ℕ) × ℕ) × List Bool, 1 ≤ wt xr.1 := fun xr ↦ one_le_wt _
  have hWΦ : ∀ xr, wt xr.1 ^ E ≤ Φ xr := fun xr ↦ by rw [hΦ]; exact Nat.le_add_right _ _
  have hWΦ' : ∀ xr, wt xr.1 ≤ Φ xr := fun xr ↦
    (Nat.le_self_pow (by omega) _).trans (hWΦ xr)
  have hlenΦ : ∀ xr, (encILNr xr).length ≤ Φ xr := fun xr ↦ by
    rw [hΦ]; exact Nat.le_add_left _ _
  -- the parts of the input
  have hy : ComputableInO Prod.fst encILNr encILN Φ Φ :=
    (ComputableInO.fst encILN encBits).mono_le hlenΦ hlenΦ
  have hr : ComputableInO Prod.snd encILNr encBits Φ Φ :=
    (ComputableInO.snd encILN encBits).mono_le hlenΦ hlenΦ
  have hx : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦ xr.1.1) encILNr
      (encPair encInstance encUnary) Φ Φ := (ComputableInO.fst _ _).comp_linear hy
  have hN : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦ xr.1.2) encILNr encUnary
      Φ Φ := (ComputableInO.snd _ _).comp_linear hy
  have hI : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦ toRaw xr.1.1.1) encILNr
      encRaw Φ Φ := (ComputableInO.of_eq (encIn := encInstance) (encMid := encRaw) (f := toRaw)
        fun I ↦ (encInstance_eq I).symm).comp_linear ((ComputableInO.fst _ _).comp_linear hx)
  have hL : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦ xr.1.1.2) encILNr
      encUnary Φ Φ := (ComputableInO.snd _ _).comp_linear hx
  -- the budget
  have hB : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦
      Par.budget xr.1.2 xr.1.1.1 xr.1.1.2) encILNr encUnary Φ Φ := by
    have hb : ∀ xr, Φ xr + wt xr.1 ^ D ≤ 2 * (Φ xr + 1) := fun xr ↦ by
      have := (Nat.pow_le_pow_right (hW1 xr) (by omega : D ≤ E)).trans (hWΦ xr)
      omega
    exact (hbud.comp' hy).mono 2 hb hb
  -- the number of coins kept
  have hz : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦
      (xr.1.2, xr.1.1, Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)) encILNr encCnt Φ Φ := by
    have hb : ∀ xr, Φ xr + (Φ xr + Φ xr) ≤ 3 * (Φ xr + 1) := fun xr ↦ by omega
    exact (hN.prod (hx.prod hB)).mono 3 hb hb
  have hcnt := comp_pow (k := 4) (W := fun xr ↦ wt xr.1) (f := coinCnt)
    (g := fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦
      (xr.1.2, xr.1.1, Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)) hCO hz (by omega) hW1 (fun xr ↦ by
    have hX := length_le_stableTime_two xr.1.1
    have := budget_le_wt xr.1
    have := stableTime_two_le_wt xr.1
    have := two_mul_le_budget xr.1.2 xr.1.1.1 xr.1.1.2
    simp only [encCnt, length_encPair, encUnary_apply, List.length_replicate] at hX ⊢
    omega) hWΦ
  -- the coins kept
  have hmap := Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO.comp_linear hr
  have htake : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦
      (xr.2.map Universal.eBit).take (coinCnt (xr.1.2, xr.1.1,
        Par.budget xr.1.2 xr.1.1.1 xr.1.1.2))) encILNr (encList encUnary) Φ Φ := by
    have hb : ∀ xr : ((Instance × ℕ) × ℕ) × List Bool, Φ xr + Φ xr +
        (encPair (encList encUnary) encUnary (((fun x ↦ x.map Universal.eBit) ∘ Prod.snd) xr,
          coinCnt (xr.1.2, xr.1.1, Par.budget xr.1.2 xr.1.1.1 xr.1.1.2))).length ≤
        10 * (Φ xr + 1) := fun xr ↦ by
      have hm : (encList encUnary (xr.2.map Universal.eBit)).length ≤ 3 * xr.2.length := by
        refine (length_encList_unary_le fun c hc ↦ ?_).trans (by rw [List.length_map])
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
        exact eBit_le_one b
      have hc : coinCnt (xr.1.2, xr.1.1, Par.budget xr.1.2 xr.1.1.1 xr.1.1.2) ≤
          Par.budget xr.1.2 xr.1.1.1 xr.1.1.2 := min_le_left _ _
      have := budget_le_wt xr.1
      have := hWΦ' xr
      have hrl : xr.2.length ≤ Φ xr := by
        have := hlenΦ xr
        simp only [encILNr, length_encPair, encBits_apply] at this
        omega
      simp only [Function.comp_apply, length_encPair, encUnary_apply, List.length_replicate]
      omega
    exact (ComputableInO.take' hmap hcnt).mono 10 hb hb
  -- the core
  have hargs : ComputableInO (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦
      (xr.1.2, toRaw xr.1.1.1, xr.1.1.2,
        (xr.2.map Universal.eBit).take (coinCnt (xr.1.2, xr.1.1,
          Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)), Par.budget xr.1.2 xr.1.1.1 xr.1.1.2))
      encILNr encCoreN Φ Φ := by
    have hb : ∀ xr, Φ xr + (Φ xr + (Φ xr + (Φ xr + Φ xr))) ≤ 5 * (Φ xr + 1) := fun xr ↦ by
      omega
    exact (hN.prod (hI.prod (hL.prod (htake.prod hB)))).mono 5 hb hb
  have hall := comp_pow (k := 10) (W := fun xr ↦ wt xr.1) (f := coreN)
    (g := fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦ (xr.1.2, toRaw xr.1.1.1, xr.1.1.2,
      (xr.2.map Universal.eBit).take (coinCnt (xr.1.2, xr.1.1,
        Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)), Par.budget xr.1.2 xr.1.1.1 xr.1.1.2))
    hRO hargs (by omega) hW1 (fun xr ↦ by
    have hX := length_le_stableTime_two xr.1.1
    have := budget_le_wt xr.1
    have := stableTime_two_le_wt xr.1
    have := two_mul_le_budget xr.1.2 xr.1.1.1 xr.1.1.2
    have hraw : (encRaw (toRaw xr.1.1.1)).length = (encInstance xr.1.1.1).length := rfl
    have htk : (encList encUnary ((xr.2.map Universal.eBit).take (coinCnt (xr.1.2, xr.1.1,
        Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)))).length ≤
        3 * Par.budget xr.1.2 xr.1.1.1 xr.1.1.2 := by
      refine (length_encList_unary_le fun c hc ↦ ?_).trans ?_
      · obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hc)
        exact eBit_le_one b
      · have := List.length_take_le (coinCnt (xr.1.2, xr.1.1,
          Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)) (xr.2.map Universal.eBit)
        have : coinCnt (xr.1.2, xr.1.1, Par.budget xr.1.2 xr.1.1.1 xr.1.1.2) ≤
            Par.budget xr.1.2 xr.1.1.1 xr.1.1.2 := min_le_left _ _
        omega
    simp only [encCoreN, length_encPair, encUnary_apply, List.length_replicate, hraw] at hX ⊢
    omega) hWΦ
  have halg : (fun xr : ((Instance × ℕ) × ℕ) × List Bool ↦ coreN (xr.1.2, toRaw xr.1.1.1,
      xr.1.1.2, (xr.2.map Universal.eBit).take (coinCnt (xr.1.2, xr.1.1,
        Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)), Par.budget xr.1.2 xr.1.1.1 xr.1.1.2)) = algN :=
    funext fun xr ↦ (algN_eq_core xr).symm
  rw [halg] at hall
  have hle : ∀ xr : ((Instance × ℕ) × ℕ) × List Bool, Φ xr ≤
      stableTime (2 * E * Par.e₁ xr.1.2 + 2 * E) xr.1.1 + (encILNr xr).length := fun xr ↦ by
    rw [hΦ]
    refine Nat.add_le_add_right ?_ _
    rw [wt, stableTime_pow]
    exact stableTime_mono (by nlinarith) _
  exact ⟨2 * E, hall.mono_le hle hle⟩

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.exists_algN_inO := @BCFGJPSSV26.Stable.exists_algN_inO
