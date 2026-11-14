-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.core_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:12:50.08854+00:00
-- url     : https://prove2.me/submissions/fde84ff7-7084-43d0-b040-202cf4d0dc08

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge
public import Definitions.Def_BCFGJPSSV26_Greedy_LMP
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDups
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_merge_spec
public import Theorems.Thm_BCFGJPSSV26_Greedy_robust_lmp

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Ctx

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

end Ctx

set_option maxHeartbeats 1000000 in
/-- **The core theorem.** -/
theorem core_spec {c : Consts} (hc : c.Good) {x : CoreIn} {X : Space x.1 x.2.1}
    (hx : CoreOK c x X) :
    core c x ≠ [] ∧ (core c x).Nodup ∧ (∀ i ∈ core c x, i < x.2.1) ∧
      (core c x).length ≤ x.2.2.1 + 6 * Rof c x.1 ∧
      ∀ O : Finset (Fin x.2.1), O.Nonempty → O.card ≤ x.2.2.1 →
        coreCost x (core c x) ≤ (ρ + 10 * c.δ) * costF X.d O := by
  have hX : (ctx c x).Hyp X := hyp_ctx hc hx
  obtain ⟨hsol, hok, -, hfree3, hcount, hreg⟩ := Ctx.merge_spec hX
  obtain ⟨hne, hnd, hlt, hlen⟩ := Ctx.toCenters_spec hX hok hreg
  have hlen1 : (ctx c x).merge.1.length = 2 * (ctx c x).ip.R := by
    have h := hsol.1
    simp only [Ctx.decH, List.length_map] at h
    exact h
  have hlen2 := Ctx.flatten_length_le hX hlen1 hfree3
  have hRk : nRegA (ctx c x).merge.1 ≤ x.2.2.1 := by
    rcases hcount with h | ⟨h, -⟩
    · exact h.le
    · exact h
  have hnR : nRegA (ctx c x).merge.1 = nReg (Ctx.decH hX (ctx c x).merge.1) :=
    Ctx.nRegA_eq hX _
  refine ⟨hne, hnd, hlt, ?_, fun O hO hOk ↦ ?_⟩
  · change (toCenters (ctx c x).merge.1).length ≤ _
    have : (ctx c x).ip.R = Rof c x.1 := rfl
    omega
  -- the cost
  have hcost := Ctx.coreCost_toCenters_le hX hsol hok
  have hf := Ctx.nη_lt_fhat hX (ctx c x).merge.2
  have hlmp := robust_lmp X (ctx c x).par hX.good hX.d1 hf hsol O hO
  have hnR' : @nReg x.2.1 (Ctx.decH hX (ctx c x).merge.1) = nRegA (ctx c x).merge.1 := hnR.symm
  rw [hnR'] at hlmp
  have hB : (x.1 : ℚ) ≤ @costF x.1 x.2.1 X.d O := Ctx.costF_ge (C := ctx c x) hX.d1 hO
  have eδ : (ctx c x).ip.δ = c.δ := rfl
  have en : (ctx c x).ip.n = x.1 := rfl
  have ek : (ctx c x).ip.k = x.2.2.1 := rfl
  have ePδ : (ctx c x).par.δ = c.δ := rfl
  have ePη : (ctx c x).par.η = (ctx c x).ip.η := rfl
  rw [ePδ, ePη] at hlmp
  have hf' : (x.1 : ℚ) * (ctx c x).ip.η < (ctx c x).fhat (ctx c x).merge.2 := hf
  have hf0 : 0 ≤ (ctx c x).fhat (ctx c x).merge.2 := by
    have : (0 : ℚ) ≤ x.1 * (ctx c x).ip.η :=
      mul_nonneg (Nat.cast_nonneg _) (hX.good.η_nonneg)
    linarith [hf']
  have hη : (nRegA (ctx c x).merge.1 : ℚ) * x.1 * (ctx c x).ip.η ≤ c.δ ^ 2 / 100 := by
    rw [hX.η_eq, eδ, en]
    exact eta_bound (by exact_mod_cast (by have := hx.two_le_n; omega : 0 < x.1))
      (by exact_mod_cast (hRk.trans hx.k_lt_n.le))
  have hopen : (O.card : ℚ) * (ctx c x).fhat (ctx c x).merge.2 ≤
      nRegA (ctx c x).merge.1 * (ctx c x).fhat (ctx c x).merge.2 + x.2.2.1 * c.δ := by
    rcases hcount with h | ⟨-, hb, -⟩
    · rw [h, ek]
      have : (O.card : ℚ) ≤ x.2.2.1 := by exact_mod_cast hOk
      have : (0 : ℚ) ≤ x.2.2.1 * c.δ := mul_nonneg (Nat.cast_nonneg _) hc.δ_pos.le
      nlinarith
    · rw [hb, Ctx.fhat_zero hX, eδ]
      have : (O.card : ℚ) ≤ x.2.2.1 := by exact_mod_cast hOk
      nlinarith [Nat.cast_nonneg (α := ℚ) (nRegA (ctx c x).merge.1), hc.δ_pos]
  exact hcost.trans (core_ineq hc.δ_pos hc.δ_le hB
    (by exact_mod_cast (by have := hx.two_le_n; omega : 1 ≤ x.1))
    (by exact_mod_cast hx.k_lt_n.le)
    (by exact_mod_cast hRk) (Nat.cast_nonneg _) hη hopen hlmp)

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.core_spec := @BCFGJPSSV26.Greedy.core_spec
