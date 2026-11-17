-- Prove2me | solution 2 for DetANN.lemma_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T19:19:55.246443+00:00
-- url     : https://prove2.me/submissions/19c10a86-fac4-4d96-8f89-55e2c61b6208
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_DetANN_HPIM_hpim_query_program_wf
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_DetANN_HPIMTree
import Theorems.Thm_DetANN_HPIM_hpim_tree_correct
import Theorems.Thm_DetANN_HPIM_hpim_preprocessing

/-!
# `lemma_3_3` from the query program `Q` (for well-formed trees), the tree correctness `M` and the
preprocessing program `P`

The tree `hpimTree Y δ` is well formed (`hpimTree_wf`): every lookup answer is a valid local index,
because the leaves of the certified BSP answer `good.min'` for a subset `good` of the local points.
-/

namespace DetANN.HPIM.WFAux

open DetANN.HPIM

variable {m : ℕ}

/-- Every leaf answer of the BSP is `< n`. -/
def LeafLt (n : ℕ) : BSP m → Prop
  | .leaf _ _ none => True
  | .leaf _ _ (some i) => i < n
  | .cut _ _ l t => LeafLt n l ∧ LeafLt n t

lemma carve_leafLt (n : ℕ) (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m)
    (hb : ∀ lo hi, LeafLt n (bld lo hi)) : ∀ d k lo hi, LeafLt n (carve tlo thi bld d k lo hi) := by
  intro d
  induction d with
  | zero => intro k lo hi; exact hb _ _
  | succ d ih =>
    intro k lo hi
    simp only [carve]
    split_ifs <;> first | exact hb _ _ | exact ih _ _ _ | exact ⟨hb _ _, ih _ _ _⟩ |
      exact ⟨ih _ _ _, hb _ _⟩ | exact ⟨hb _ _, ih _ _ _, hb _ _⟩

lemma build_leafLt {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ) :
    ∀ f lo hi, LeafLt n (build pts r c f lo hi) := by
  intro f
  induction f with
  | zero => intro lo hi; simp [build, LeafLt]
  | succ f ih =>
    intro lo hi
    simp only [build]
    split_ifs
    · exact Fin.isLt _
    · exact carve_leafLt n _ _ _ ih _ _ _ _
    · split
      · trivial
      · exact ⟨ih _ _, ih _ _⟩
    · trivial

lemma sub_leafLt {n : ℕ} : ∀ (T : BSP m) (p : List Bool) (t : BSP m), LeafLt n T → T.sub p = some t →
    LeafLt n t := by
  intro T
  induction T with
  | leaf lo hi a =>
    intro p t h hp
    cases p with
    | nil => simp [BSP.sub] at hp; rw [← hp]; exact h
    | cons b p => simp [BSP.sub] at hp
  | cut lo hi l r ihl ihr =>
    intro p t h hp
    cases p with
    | nil => simp [BSP.sub] at hp; rw [← hp]; exact h
    | cons b p =>
      cases b
      · exact ihl p t h.1 hp
      · exact ihr p t h.2 hp

lemma ans_lt {n : ℕ} (t : BSP m) (h : LeafLt n t) {i : ℕ} (hi : t.ans = some i) : i < n := by
  cases t with
  | leaf lo hi a =>
    cases a with
    | none => simp [BSP.ans] at hi
    | some j => simp [BSP.ans] at hi; rw [← hi]; exact h
  | cut => simp [BSP.ans] at hi

lemma balance_ansLt {n : ℕ} (T : BSP m) (hT : LeafLt n T) :
    ∀ f p R, (balance T f p R).AnsLt n := by
  have hleaf : ∀ p, (BoxTree.leaf ((T.sub p).bind BSP.ans) : BoxTree m).AnsLt n := by
    intro p
    rcases h : (T.sub p).bind BSP.ans with _ | i
    · trivial
    · obtain ⟨t, ht, hti⟩ := Option.bind_eq_some_iff.1 h
      exact ans_lt t (sub_leafLt T p t hT ht) hti
  intro f
  induction f with
  | zero => intro p R; trivial
  | succ f ih =>
    intro p R
    simp only [balance]
    split_ifs
    · exact hleaf p
    · split
      · exact hleaf p
      · split
        · trivial
        · exact ⟨ih _ _, ih _ _⟩

lemma lookupTree_ansLt {n : ℕ} (pts : Fin n → Fin m → ℝ) (r c δ : ℝ) :
    (lookupTree pts r c δ).AnsLt n := by
  unfold lookupTree
  split_ifs with hn
  · exact ⟨balance_ansLt _ (build_leafLt pts r c _ _ _) _ _ _, trivial⟩
  · trivial

lemma hpimNode_wf {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) :
    ∀ f S, (hpimNode Y δ f S).WF := by
  intro f
  induction f with
  | zero => intro S; simp [hpimNode, HTree.WF]
  | succ f ih =>
    intro S
    simp only [hpimNode]
    by_cases hS : S.card ≤ 1
    · rw [if_pos hS]; simp [HTree.WF]
    · rw [if_neg hS]
      exact (show (∀ i, (ZOf Y δ S i).AnsLt S.card) ∧ (∀ i, (hpimNode Y δ f (compBotOf Y S i)).WF) ∧
        (hpimNode Y δ f (repsOf Y S)).WF from
        ⟨fun i => lookupTree_ansLt _ _ _ _, fun i => ih _, ih _⟩)

lemma hpimTree_wf {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) : (hpimTree Y δ).WF :=
  hpimNode_wf Y δ _ _

end DetANN.HPIM.WFAux

open DetANN DetANN.HPIM in
theorem solution :
    ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
      ∃ C : ℝ, 1 < C ∧ ∃ K C' : ℕ, ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
          ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
            IsDetANNStructure Pre Qry Y δ (1 + δ)
              ((C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
              ((C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
              ((C' : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2) := by
  obtain ⟨Qry, hQdet, c₀, hQ⟩ := hpim_query_program_wf
  obtain ⟨C₁, hM⟩ := hpim_tree_correct
  obtain ⟨Pre, hPdet, C, hC, K, CP, hP⟩ := hpim_preprocessing
  refine ⟨Pre, Qry, hPdet, hQdet, C, hC, K, max CP (2 * c₀ * C₁), ?_⟩
  intro m N hm hN Y hY δ hδ hδ'
  have hNd : 1 < (N : ℝ) / δ := by
    rw [one_lt_div hδ]; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog : 0 < Real.log (N / δ) := Real.log_pos hNd
  have hCP : (CP : ℝ) ≤ (max CP (2 * c₀ * C₁) : ℕ) := by exact_mod_cast le_max_left _ _
  have hCQ : ((2 * c₀ * C₁ : ℕ) : ℝ) ≤ (max CP (2 * c₀ * C₁) : ℕ) := by exact_mod_cast le_max_right _ _
  obtain ⟨t, hhalt, hwork, hcells, hI1, hlay⟩ := hP m N hm hN Y hY δ hδ hδ'
  refine ⟨t, hhalt, ?_, ?_, ?_⟩
  · refine hwork.trans ?_
    have h1 : (0 : ℝ) ≤ ((N : ℝ) + m) ^ K := by positivity
    have h2 : (0 : ℝ) ≤ (C / δ) ^ ((K : ℝ) * m) := by positivity
    have h3 : (0 : ℝ) ≤ Real.log (N / δ) ^ K := pow_nonneg hlog.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCP h1) h2) h3
  · refine hcells.trans ?_
    have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (C / δ) ^ ((K : ℝ) * m) := by positivity
    have h3 : (0 : ℝ) ≤ Real.log (N / δ) ^ K := pow_nonneg hlog.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCP h1) h2) h3
  · intro q
    obtain ⟨t', hh, hw, hp⟩ := hQ m _ (hpimTree Y δ) q hm (WFAux.hpimTree_wf Y δ) hI1 hlay
    obtain ⟨⟨k, hk, hann⟩, hcost⟩ := hM m N hm hN Y hY δ hδ hδ' q
    refine ⟨t', hh, ?_, k, ?_, hann⟩
    · have hw' : ((PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y δ) detTape t) q)
          detTape t').work : ℝ) ≤ (c₀ : ℝ) * ((m : ℝ) + 1) * ((hpimTree Y δ).cost q : ℝ) := by
        exact_mod_cast hw
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hc0 : (0 : ℝ) ≤ c₀ := by positivity
      have hL : 0 ≤ Real.log (N / δ) ^ 2 := by positivity
      calc _ ≤ (c₀ : ℝ) * ((m : ℝ) + 1) * ((hpimTree Y δ).cost q : ℝ) := hw'
        _ ≤ (c₀ : ℝ) * ((m : ℝ) + 1) * (C₁ * m * Real.log (N / δ) ^ 2) := by gcongr
        _ ≤ (c₀ : ℝ) * (2 * m) * (C₁ * m * Real.log (N / δ) ^ 2) := by gcongr; linarith
        _ = ((2 * c₀ * C₁ : ℕ) : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2 := by push_cast; ring
        _ ≤ _ := by gcongr
    · rw [hp, hk]
