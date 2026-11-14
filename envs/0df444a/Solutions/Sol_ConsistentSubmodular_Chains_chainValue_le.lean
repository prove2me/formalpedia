-- Prove2me | solution 1 for ConsistentSubmodular.Chains.chainValue_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:38.861204+00:00
-- url     : https://prove2.me/submissions/4ca9513a-d42e-43b2-a134-66dcd32cc80b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_bounds
import Theorems.Thm_ConsistentSubmodular_Chains_twoEdgeRatio_le
import Theorems.Thm_ConsistentSubmodular_Chains_collapse_le
import Theorems.Thm_ConsistentSubmodular_Chains_threeEdge_le_bound
import Theorems.Thm_ConsistentSubmodular_Chains_threeEdgeBound_antitoneOn
import Theorems.Thm_ConsistentSubmodular_Chains_threeEdgeBound_collapseBound_le
import Theorems.Thm_ConsistentSubmodular_Chains_IsDescendingChain_skip
import Theorems.Thm_ConsistentSubmodular_Chains_tail_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_lt_one : xiStar < 1 := xiStar_root.2.1

theorem qStar_pos : 0 < qStar := div_pos (by linarith [xiStar_lt_one]) xiStar_pos

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- **Inequality (15)**: `φ(x, y) + φ(y, 1) ≤ q` for `x ≥ y ≥ 1`. -/
theorem twoEdge_le {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y 1 ≤ qStar := by
  have h := twoEdgeRatio_le hy hyx
  have hD : 0 < x + y - 1 := by linarith
  unfold twoEdgeRatio at h
  rw [div_le_iff₀ hD] at h
  unfold edgeValue
  linarith

theorem one_sub_qStar_pos : 0 < 1 - qStar := by linarith [qStar_bounds.2]

theorem four_thirds_lt_collapseBound : (4 : ℝ) / 3 < collapseBound := by
  rw [collapseBound, lt_div_iff₀ one_sub_qStar_pos]
  linarith [qStar_bounds.1]

/-- A positive edge `x → y` has `y < h(x) = (1 + q) x - q x²`. -/
theorem lt_of_edgeValue_pos {x y : ℝ} (hx : 0 < x) (h : 0 < edgeValue x y) :
    y < (1 + qStar) * x - qStar * x ^ 2 := by
  unfold edgeValue at h
  have h' : y / x < 1 - qStar * (x - 1) := by linarith
  rw [div_lt_iff₀ hx] at h'
  nlinarith

/-- The second vertex of a positive edge satisfies `d_1 < T < 31/20`, where
`T = (1 + q)²/(4q)` is the maximum of `h`; the bound on `T` uses (13). -/
theorem second_lt {x y : ℝ} (hx : 1 ≤ x) (h : 0 < edgeValue x y) : y < 31 / 20 := by
  have hq := qStar_bounds
  have hy := lt_of_edgeValue_pos (by linarith) h
  nlinarith [sq_nonneg (2 * qStar * x - (1 + qStar)),
    mul_pos (sub_pos.mpr hq.1) (sub_pos.mpr hq.2)]

/-- The third vertex of a chain with two positive edges satisfies
`d_2 < h(31/20) = 31/20 - 341 q/400 < 4/3`, because `h` increases on `[1, 31/20]`
by (13). -/
theorem third_lt {y z : ℝ} (hy : 1 ≤ y) (hy' : y < 31 / 20) (h : 0 < edgeValue y z) :
    z < 4 / 3 := by
  have hq := qStar_bounds
  have hz := lt_of_edgeValue_pos (by linarith) h
  have hinc : 0 ≤ 1 + qStar - qStar * (31 / 20 + y) := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 31 / 20 - y by linarith) hinc]

/-- Three-edge chains `x → y → z → 1` have value at most `q`: by (16) and (15) if
`y ≤ L`, and by `F(y) ≤ F(L) ≤ q` if `y ≥ L`. -/
theorem threeEdge_le {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y z + edgeValue z 1 ≤ qStar := by
  rcases le_total y collapseBound with hyL | hyL
  · have h18 := collapse_le (le_refl 1) hz hzy hyL
    have h17 := twoEdge_le (le_trans hz hzy) hyx
    linarith
  · have hF := threeEdge_le_bound hz hzy hyx
    have hmono := threeEdgeBound_antitoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hyL) hyL
    linarith [threeEdgeBound_collapseBound_le]

theorem chainValue_cons_cons (x y : ℝ) (rest : List ℝ) :
    chainValue (x :: y :: rest) = edgeValue x y + chainValue (y :: rest) := rfl

namespace IsDescendingChain

variable {x y z : ℝ} {rest : List ℝ}

theorem le_head (h : IsDescendingChain (x :: y :: rest)) : y ≤ x :=
  (List.isChain_cons_cons.mp h.1).1

theorem one_le {L : List ℝ} (h : IsDescendingChain L) {w : ℝ} (hw : w ∈ L) : 1 ≤ w :=
  h.2.1 w hw

theorem tail (h : IsDescendingChain (x :: y :: rest)) : IsDescendingChain (y :: rest) :=
  ⟨(List.isChain_cons_cons.mp h.1).2, fun w hw => h.2.1 w (List.mem_cons_of_mem x hw),
    by rw [← List.getLast?_cons_cons (a := x)]; exact h.2.2⟩

theorem eq_one_of_singleton (h : IsDescendingChain [x]) : x = 1 := by
  have h2 := h.2.2
  rw [List.getLast?_singleton] at h2
  exact Option.some.inj h2

end IsDescendingChain

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution (L : List ℝ) (hL : IsDescendingChain L) : chainValue L ≤ qStar := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    match L, hL with
    | [], _ => exact qStar_pos.le
    | [_], _ => exact qStar_pos.le
    | x :: y :: rest, hL =>
      have hyx := hL.le_head
      have hx1 : 1 ≤ x := hL.one_le (by simp)
      have hy1 : 1 ≤ y := hL.one_le (by simp)
      rw [chainValue_cons_cons]
      by_cases h1 : edgeValue x y ≤ 0
      · -- Delete the first vertex.
        have := ih (y :: rest).length (by simp [← h]) (y :: rest) hL.tail rfl
        linarith
      · rw [not_le] at h1
        cases rest with
        | nil =>
          have hy : y = 1 := hL.tail.eq_one_of_singleton
          subst hy
          have h17 := twoEdge_le (le_refl 1) hx1
          simp only [chainValue, edgeValue] at h17 ⊢
          norm_num at h17 ⊢
          linarith
        | cons z rest' =>
          have hzy := hL.tail.le_head
          have hz1 : 1 ≤ z := hL.one_le (by simp)
          rw [chainValue_cons_cons]
          by_cases h2 : edgeValue y z ≤ 0
          · -- Delete the second vertex: `φ(x, y) ≤ φ(x, z)`.
            have hskip := ih (x :: z :: rest').length (by simp [← h]) (x :: z :: rest') hL.skip rfl
            rw [chainValue_cons_cons] at hskip
            have hxz : edgeValue x y ≤ edgeValue x z := by
              unfold edgeValue
              have : z / x ≤ y / x := div_le_div_of_nonneg_right hzy (by linarith)
              linarith
            linarith
          · rw [not_le] at h2
            have hz' := third_lt hy1 (second_lt hx1 h1) h2
            have htail := tail_le z rest' hL.tail.tail
              (by linarith [four_thirds_lt_collapseBound])
            have h3 := threeEdge_le hz1 hzy hyx
            linarith

end
