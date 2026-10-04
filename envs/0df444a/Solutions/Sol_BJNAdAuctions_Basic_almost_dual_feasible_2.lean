-- Prove2me | solution 2 for BJNAdAuctions.Basic.almost_dual_feasible
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:02:21.970265+00:00
-- url     : https://prove2.me/submissions/7c9d96d5-bef9-4edb-a853-882d84b9823f

import Theorems.Thm_BJNAdAuctions_Basic_x_lower_bound
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

/-!
# Ad-Auctions, Theorem 1, Claim (3): almost feasibility of the dual (packing) solution

With `c = (1 + R)^(1/R)` and every bid at most `R` times its buyer's budget, each buyer `i`
receives total allocated bids `A i = ∑_j b i j y i j ≤ B i + max_j b i j`, and the amount
actually charged satisfies `(1 - R) A i ≤ spent i`.

* The algorithm allocates to buyer `i` only while `x i < 1`.  The platform theorem
  `BJNAdAuctions.Basic.x_lower_bound` (Inequality (1), already proved) gives
  `x i ≥ (c^{S/B} - 1)/(c - 1)` after any prefix, `S` the allocated bids so far.  Applied
  at the prefix just before the *last* allocation `j*` of `i`, the guard `x i < 1` forces
  `S < B i`, so `A i = S + b i j* ≤ B i + max_j b i j`.
* The charge rule `spent ← spent + min b (B - spent)` keeps `spent i = min (B i) A i` exactly,
  from which `(1 - R) A i ≤ min (B i) A i` follows by a case split on `R ≤ 1` (using
  `A ≤ B + R·B` from the first part when `A > B`).
-/

open BJNAdAuctions.Basic

open scoped Classical

namespace BJNClaim3Aux

variable {I : Type*} [Fintype I] {m : ℕ}

/-- Columns not yet processed are unallocated: after `k` steps, `y i j = 0` for all `j ≥ k`. -/
private lemma y_zero_of_ge (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) :
    ∀ k ≤ m, ∀ (i : I) (j : Fin m), k ≤ (j : ℕ) → (runPrefix inst c sel k).y i j = 0
  | 0, _, i, j, _ => by simp [runPrefix, State.init]
  | k + 1, hk, i, j, hj => by
      have hkm : k < m := by omega
      rw [runPrefix, dif_pos hkm]
      simp only [step]
      split
      · exact y_zero_of_ge inst c sel k (by omega) i j (by omega)
      · rename_i hguard
        rcases eq_or_ne i (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) with rfl | hi
        · simp only [Function.update_self]
          have hne : j ≠ (⟨k, hkm⟩ : Fin m) := fun hcon => by
            have h9 := congrArg Fin.val hcon
            simp only [Fin.val_mk] at h9
            omega
          rw [Function.update_of_ne hne]
          exact y_zero_of_ge inst c sel k (by omega) _ j (by omega)
        · simp only [Function.update_of_ne hi]
          exact y_zero_of_ge inst c sel k (by omega) i j (by omega)

/-- Columns freeze after their own step: for `j < k`, `y` after `k` steps equals `y` after
`j + 1` steps. -/
private lemma y_frozen (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) :
    ∀ k ≤ m, ∀ (i : I) (j : Fin m), (j : ℕ) < k →
      (runPrefix inst c sel k).y i j = (runPrefix inst c sel ((j : ℕ) + 1)).y i j
  | 0, _, i, j, hj => by omega
  | k + 1, hk, i, j, hj => by
      have hkm : k < m := by omega
      rw [runPrefix, dif_pos hkm]
      simp only [step]
      split
      · rename_i hguard
        rcases eq_or_ne (j : ℕ) k with hjk | hjk
        · rw [show ((j : ℕ) + 1) = k + 1 by omega, runPrefix, dif_pos hkm]
          simp only [step]
          rw [if_pos hguard]
        · rw [y_frozen inst c sel k (by omega) i j (by omega)]
      · rename_i hguard
        rcases eq_or_ne (j : ℕ) k with hjk | hjk
        · rw [show ((j : ℕ) + 1) = k + 1 by omega, runPrefix, dif_pos hkm]
          simp only [step]
          rw [if_neg hguard]
        · have hne : j ≠ ⟨k, hkm⟩ := fun hcon => by
            have h9 := congrArg Fin.val hcon
            simp only [Fin.val_mk] at h9
            omega
          rw [← y_frozen inst c sel k (by omega) i j (by omega)]
          rcases eq_or_ne i (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) with rfl | hi
          · simp only [Function.update_self, Function.update_of_ne hne]
          · simp only [Function.update_of_ne hi]

/-- Every allocated fraction is `0` or `1`. -/
private lemma y_mem01 (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) :
    ∀ k ≤ m, ∀ (i : I) (j : Fin m), (runPrefix inst c sel k).y i j = 0 ∨
      (runPrefix inst c sel k).y i j = 1
  | 0, _, i, j => by simp [runPrefix, State.init]
  | k + 1, hk, i, j => by
      have hkm : k < m := by omega
      rw [runPrefix, dif_pos hkm]
      simp only [step]
      split
      · exact y_mem01 inst c sel k (by omega) i j
      · rename_i hguard
        rcases eq_or_ne i (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) with rfl | hi
        · simp only [Function.update_self]
          rcases eq_or_ne j ⟨k, hkm⟩ with rfl | hj
          · simp only [Function.update_self]
            exact Or.inr trivial
          · simp only [Function.update_of_ne hj]
            exact y_mem01 inst c sel k (by omega) _ j
        · simp only [Function.update_of_ne hi]
          exact y_mem01 inst c sel k (by omega) i j

/-- The charge rule keeps `spent i = min (B i) (allocated bids so far)`. -/
private lemma spent_eq (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I) :
    ∀ k ≤ m, ∀ (i : I),
      (runPrefix inst c sel k).spent i
        = min (inst.B i) (∑ j, inst.b i j * (runPrefix inst c sel k).y i j)
  | 0, _, i => by
      simp only [runPrefix, State.init, mul_zero, Finset.sum_const_zero,
        min_eq_right (le_of_lt (inst.B_pos i))]
  | k + 1, hk, i => by
      have hkm : k < m := by omega
      rcases Classical.em (1 ≤ (runPrefix inst c sel k).x (sel (runPrefix inst c sel k).x ⟨k, hkm⟩))
        with hguard | hguard
      · -- guard holds: the state is unchanged
        have hgoal : (runPrefix inst c sel (k + 1)).spent i
            = min (inst.B i) (∑ j, inst.b i j * (runPrefix inst c sel (k + 1)).y i j) := by
          rw [runPrefix, dif_pos hkm]
          simp only [step, if_pos hguard]
          exact spent_eq inst c sel k (by omega) i
        exact hgoal
      · -- guard fails: the selected buyer is updated
        set X := sel (runPrefix inst c sel k).x ⟨k, hkm⟩ with hXdef
        have hguard' : ¬1 ≤ (runPrefix inst c sel k).x
            (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) := hguard
        have hyJ : (runPrefix inst c sel k).y X ⟨k, hkm⟩ = 0 :=
          y_zero_of_ge inst c sel k (by omega) X ⟨k, hkm⟩ (le_refl k)
        have hyJ' : (runPrefix inst c sel k).y (sel (runPrefix inst c sel k).x ⟨k, hkm⟩)
            ⟨k, hkm⟩ = 0 := hyJ
        have hb : 0 ≤ inst.b X ⟨k, hkm⟩ := inst.b_nonneg X _
        have hB : 0 < inst.B X := inst.B_pos X
        rcases eq_or_ne i X with rfl | hi
        · have hspent : (runPrefix inst c sel (k + 1)).spent X
              = (runPrefix inst c sel k).spent X
                + min (inst.b X ⟨k, hkm⟩) (inst.B X - (runPrefix inst c sel k).spent X) := by
            simp only [runPrefix, dif_pos hkm, step, if_neg hguard', hXdef,
              Function.update_self]
          have hpt : ∀ j : Fin m, inst.b X j * (runPrefix inst c sel (k + 1)).y X j
              = inst.b X j * (runPrefix inst c sel k).y X j
                + (if j = ⟨k, hkm⟩ then inst.b X ⟨k, hkm⟩ else 0) := by
            intro j
            rcases eq_or_ne j ⟨k, hkm⟩ with rfl | hj
            · simp only [runPrefix, dif_pos hkm, step, if_neg hguard', hXdef,
                Function.update_self]
              simp [hyJ']
            · simp only [runPrefix, dif_pos hkm, step, if_neg hguard', hXdef,
                Function.update_self, Function.update_of_ne hj, if_neg hj]
              ring
          have hsum : (∑ j, inst.b X j * (runPrefix inst c sel (k + 1)).y X j)
              = (∑ j, inst.b X j * (runPrefix inst c sel k).y X j) + inst.b X ⟨k, hkm⟩ := by
            rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib]
            congr 1
            exact Fintype.sum_ite_eq' (⟨k, hkm⟩ : Fin m) (fun _ => inst.b X ⟨k, hkm⟩)
          have hgoal : (runPrefix inst c sel (k + 1)).spent X
              = min (inst.B X) (∑ j, inst.b X j * (runPrefix inst c sel (k + 1)).y X j) := by
            rw [hspent, hsum, spent_eq inst c sel k (by omega) X]
            rcases le_total (∑ j, inst.b X j * (runPrefix inst c sel k).y X j) (inst.B X)
              with hS | hS
            · rw [min_eq_right hS]
              simp only [min_def]
              split_ifs <;> linarith
            · rw [min_eq_left hS]
              simp only [min_def]
              split_ifs <;> linarith
          exact hgoal
        · -- other buyers are untouched
          have hi' : i ≠ sel (runPrefix inst c sel k).x ⟨k, hkm⟩ := hi
          have hspent : (runPrefix inst c sel (k + 1)).spent i
              = (runPrefix inst c sel k).spent i := by
            simp only [runPrefix, dif_pos hkm, step, if_neg hguard', hXdef,
              Function.update_of_ne hi']
          have hy : ∀ j, (runPrefix inst c sel (k + 1)).y i j
              = (runPrefix inst c sel k).y i j := by
            intro j
            simp only [runPrefix, dif_pos hkm, step, if_neg hguard', hXdef,
              Function.update_of_ne hi']
          have hgoal : (runPrefix inst c sel (k + 1)).spent i
              = min (inst.B i) (∑ j, inst.b i j * (runPrefix inst c sel (k + 1)).y i j) := by
            rw [hspent, spent_eq inst c sel k (by omega) i]
            congr 1
            exact Finset.sum_congr rfl (fun j _ => by rw [hy j])
          exact hgoal

/-- If the algorithm allocates product `k` to buyer `i`, then `x i < 1` held before step `k`. -/
private lemma x_lt_one_of_alloc (inst : Instance I m) (c : ℝ) (sel : (I → ℝ) → Fin m → I)
    {k : ℕ} (hkm : k < m) (i : I)
    (h : (runPrefix inst c sel (k + 1)).y i ⟨k, hkm⟩ = 1) :
    (runPrefix inst c sel k).x i < 1 := by
  rw [runPrefix, dif_pos hkm] at h
  simp only [step] at h
  split at h
  · rw [y_zero_of_ge inst c sel k (by omega) i ⟨k, hkm⟩ (le_refl k)] at h
    exact absurd h (by norm_num)
  · rename_i hguard
    rcases eq_or_ne i (sel (runPrefix inst c sel k).x ⟨k, hkm⟩) with rfl | hi
    · simp only [Function.update_self, Function.update_self] at h
      exact not_le.1 hguard
    · simp only [Function.update_of_ne hi,
        y_zero_of_ge inst c sel k (by omega) i ⟨k, hkm⟩ (le_refl k)] at h
      exact absurd h (by norm_num)

end BJNClaim3Aux

open BJNAdAuctions.Basic BJNClaim3Aux

theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (i : I) :
    ∑ j, inst.b i j * (run inst ((1 + R) ^ (1 / R)) sel).y i j ≤ inst.B i + (⨆ j, inst.b i j) ∧
    (1 - R) * ∑ j, inst.b i j * (run inst ((1 + R) ^ (1 / R)) sel).y i j ≤
      (run inst ((1 + R) ^ (1 / R)) sel).spent i := by
  set c := (1 + R) ^ (1 / R) with hc
  have hc1 : 1 < c := Real.one_lt_rpow (by linarith) (by positivity)
  have hB : 0 < inst.B i := inst.B_pos i
  have hbnn : ∀ j, 0 ≤ inst.b i j := fun j => inst.b_nonneg i j
  rw [run]
  set A := ∑ j, inst.b i j * (runPrefix inst c sel m).y i j with hA
  have hAnn : 0 ≤ A := by
    refine Finset.sum_nonneg (fun j _ => ?_)
    rcases y_mem01 inst c sel m (by omega) i j with h | h <;> simp [h, hbnn j]
  have hbdd : BddAbove (Set.range (inst.b i)) := Finite.bddAbove_range _
  have hsupnn : 0 ≤ ⨆ j, inst.b i j := Real.iSup_nonneg (fun j => hbnn j)
  -- Part 1
  have key1 : A ≤ inst.B i + (⨆ j, inst.b i j) := by
    rcases le_total A (inst.B i) with hAB | hAB
    · linarith
    · by_contra hcon
      push Not at hcon
      exfalso
      -- the support is nonempty since A > B ≥ 0
      have hsup_ne : (Finset.univ.filter (fun j => (runPrefix inst c sel m).y i j = 1)).Nonempty := by
        by_contra hempty
        push Not at hempty
        have hyvzero : ∀ j : Fin m, (runPrefix inst c sel m).y i j = 0 := by
          intro j
          rcases y_mem01 inst c sel m (by omega) i j with h0 | h1
          · exact h0
          · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1⟩) (by
              intro hmem
              rw [hempty] at hmem
              exact absurd hmem (by simp))
        have hzero : A = 0 := by
          refine Finset.sum_eq_zero (fun j _ => ?_)
          simp [hyvzero j]
        linarith
      set T : Finset (Fin m) := Finset.univ.filter (fun j => (runPrefix inst c sel m).y i j = 1)
        with hT
      have hTne : T.Nonempty := hsup_ne
      set jstar := T.max' hTne with hjstar
      have hjstarT : jstar ∈ T := T.max'_mem hTne
      have hyle : (runPrefix inst c sel m).y i jstar = 1 :=
        (Finset.mem_filter.mp hjstarT).2
      have hvalm : (jstar : ℕ) < m := by
        by_contra hcon2
        push Not at hcon2
        rw [y_zero_of_ge inst c sel m (le_refl m) i jstar hcon2] at hyle
        exact absurd hyle (by norm_num)
      -- guard at the allocation step of jstar
      have hstep : (runPrefix inst c sel ((jstar : ℕ) + 1)).y i ⟨(jstar : ℕ), hvalm⟩ = 1 := by
        have het : (⟨(jstar : ℕ), hvalm⟩ : Fin m) = jstar :=
          Fin.val_injective (by simp)
        have hfroz := y_frozen inst c sel m (by omega) i jstar (by omega)
        rw [het, ← hfroz]
        exact hyle
      have hxlt : (runPrefix inst c sel (jstar : ℕ)).x i < 1 :=
        x_lt_one_of_alloc inst c sel hvalm i hstep
      -- Inequality (1) at the prefix just before the last allocation
      have hxl := x_lower_bound inst R hR hbR sel (jstar : ℕ) (by omega) i
      rw [← hc] at hxl
      set S := ∑ j, inst.b i j * (runPrefix inst c sel (jstar : ℕ)).y i j with hS
      have hSB : S < inst.B i := by
        have h3 : 1 / (c - 1) * (c ^ (S / inst.B i) - 1) < 1 := by
          refine lt_of_le_of_lt hxl hxlt
        have h4 : (0 : ℝ) < c - 1 := by linarith
        have h5 : c ^ (S / inst.B i) - 1 < c - 1 := by
          have h5' := mul_lt_mul_of_pos_right h3 h4
          field_simp at h5'
          linarith
        have h6 : S / inst.B i < 1 := by
          by_contra hcon3
          push Not at hcon3
          have hle := Real.rpow_le_rpow_of_exponent_le (le_of_lt hc1) hcon3
          rw [Real.rpow_one] at hle
          linarith
        exact (div_lt_one₀ hB).mp h6
      -- A = S + b i jstar
      have hAeq : A = S + inst.b i jstar := by
        have hpt : ∀ j : Fin m, inst.b i j * (runPrefix inst c sel m).y i j
            = inst.b i j * (runPrefix inst c sel (jstar : ℕ)).y i j
              + (if j = jstar then inst.b i jstar else 0) := by
          intro j
          rcases lt_trichotomy (j : ℕ) (jstar : ℕ) with hlt | heq | hgt
          · have hyeq : (runPrefix inst c sel m).y i j
                = (runPrefix inst c sel (jstar : ℕ)).y i j := by
              rw [y_frozen inst c sel m (by omega) i j (by omega),
                ← y_frozen inst c sel (jstar : ℕ) (by omega) i j hlt]
            simp [hyeq]
            have : j ≠ jstar := fun hcon4 => by
              have h9 := congrArg Fin.val hcon4
              omega
            simp [this]
          · have hjjs : j = jstar := Fin.val_injective heq
            subst hjjs
            have hy0 : (runPrefix inst c sel (jstar : ℕ)).y i jstar = 0 :=
              y_zero_of_ge inst c sel (jstar : ℕ) (by omega) i jstar (le_refl _)
            simp [hyle, hy0]
          · have hjnotT : j ∉ T := by
              intro hmem
              have hjle := T.le_max' j hmem
              have : (j : ℕ) ≤ (jstar : ℕ) := by omega
              omega
            have hym : (runPrefix inst c sel m).y i j = 0 := by
              rcases y_mem01 inst c sel m (by omega) i j with h0 | h1
              · exact h0
              · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1⟩) hjnotT
            have hyk : (runPrefix inst c sel (jstar : ℕ)).y i j = 0 :=
              y_zero_of_ge inst c sel (jstar : ℕ) (by omega) i j (by omega)
            have hjne : j ≠ jstar := fun hcon4 => by
              have h9 := congrArg Fin.val hcon4
              omega
            simp [hym, hyk, hjne]
        rw [hA, hS, Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib]
        congr 1
        exact Fintype.sum_ite_eq' jstar (fun _ => inst.b i jstar)
      -- conclusion of part 1
      have hsuple : inst.b i jstar ≤ ⨆ j, inst.b i j := le_ciSup hbdd jstar
      linarith
  -- Part 2
  have hspent : (runPrefix inst c sel m).spent i = min (inst.B i) A :=
    spent_eq inst c sel m (by omega) i
  refine ⟨key1, ?_⟩
  rw [hspent]
  rcases le_total A (inst.B i) with hAB | hAB
  · rw [min_eq_right hAB]
    nlinarith [mul_nonneg hAnn (by linarith : (0 : ℝ) ≤ R)]
  · rw [min_eq_left hAB]
    rcases le_total R 1 with hR1 | hR1
    · have hsupR : (⨆ j, inst.b i j) ≤ R * inst.B i := by
        refine Real.sSup_le ?_ (mul_nonneg hR.le hB.le)
        rintro x ⟨j, rfl⟩
        exact hbR i j
      have hRR : R * R ≤ 1 := by nlinarith
      nlinarith
    · have hnonpos : (1 - R) * A ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith : (1 : ℝ) - R ≤ 0) hAnn
      linarith
