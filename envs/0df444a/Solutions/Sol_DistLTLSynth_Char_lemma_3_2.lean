-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:17:03.627288+00:00
-- url     : https://prove2.me/submissions/5228b9c6-bc9c-4593-a37b-b8c048793a58

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Theorems.Thm_DistLTLSynth_Char_lemma_2_4
import Theorems.Thm_DistLTLSynth_Char_lemma_3_6
import Theorems.Thm_DistLTLSynth_Char_lemma_5_2
import Theorems.Thm_DistLTLSynth_Char_lemma_6_15
import Theorems.Thm_DistLTLSynth_Char_lemma_6_16

namespace DistLTLSynth.Char.Lemma32Aux
open DistLTLSynth.Char

/-! ### Geometric helpers for missing-prefix implies non-dense image -/

def stepJ (a : ℕ) (g : CommGraph) : ℕ :=
  3 * a + if a % 2 = 0 then delta g else 2 - delta g

lemma delta_le (g : CommGraph) : delta g ≤ 2 := by
  cases g <;> simp [delta]

lemma delta_inj {x y : CommGraph} (h : delta x = delta y) : x = y := by
  cases x <;> cases y <;> simp_all [delta]

lemma stepJ_bounds (a : ℕ) (g : CommGraph) : 3 * a ≤ stepJ a g ∧ stepJ a g ≤ 3 * a + 2 := by
  have := delta_le g
  unfold stepJ
  split <;> omega

lemma jIdx_append (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = stepJ (jIdx h) g := by
  unfold jIdx stepJ
  rw [List.foldl_append]
  rfl

lemma jIdx_lt (gs : List CommGraph) : jIdx gs < 3 ^ gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [jIdx]
  | append_singleton gs g ih =>
    rw [jIdx_append, List.length_append, List.length_singleton, pow_succ]
    have := stepJ_bounds (jIdx gs) g
    omega

lemma pre_succ_gen {α : Type} (w : ℕ → α) (r : ℕ) : pre w (r + 1) = pre w r ++ [w r] := by
  unfold pre
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

lemma pre_length_gen {α : Type} (w : ℕ → α) (r : ℕ) : (pre w r).length = r := by
  simp [pre]

noncomputable def lo (w : ℕ → CommGraph) (r : ℕ) : ℝ :=
  (jIdx (pre w r) : ℝ) / 3 ^ r

lemma lo_mono (w : ℕ → CommGraph) : Monotone (lo w) := by
  apply monotone_nat_of_le_succ
  intro r
  have hb := stepJ_bounds (jIdx (pre w r)) (w r)
  unfold lo
  rw [pre_succ_gen, jIdx_append]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (3 * (jIdx (pre w r)) : ℝ) ≤ (stepJ (jIdx (pre w r)) (w r) : ℝ) := by exact_mod_cast hb.1
  rw [pow_succ]
  nlinarith [pow_pos (show (0 : ℝ) < 3 by norm_num) r]

lemma hi_anti (w : ℕ → CommGraph) : Antitone (fun r => lo w r + 1 / 3 ^ r) := by
  apply antitone_nat_of_succ_le
  intro r
  have hb := stepJ_bounds (jIdx (pre w r)) (w r)
  unfold lo
  rw [pre_succ_gen, jIdx_append]
  have h3 : (stepJ (jIdx (pre w r)) (w r) : ℝ) ≤ 3 * (jIdx (pre w r)) + 2 := by exact_mod_cast hb.2
  have hp : (0 : ℝ) < 3 ^ r := by positivity
  have e1 : (stepJ (jIdx (pre w r)) (w r) : ℝ) / 3 ^ (r + 1) + 1 / 3 ^ (r + 1)
      = ((stepJ (jIdx (pre w r)) (w r) : ℝ) + 1) / (3 * 3 ^ r) := by rw [pow_succ]; ring
  have e2 : (jIdx (pre w r) : ℝ) / 3 ^ r + 1 / 3 ^ r = ((jIdx (pre w r) : ℝ) + 1) / 3 ^ r := by
    ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) hp]
  nlinarith

lemma lo_le_hi (w : ℕ → CommGraph) (s r : ℕ) : lo w s ≤ lo w r + 1 / 3 ^ r := by
  rcases le_total s r with h | h
  · have := lo_mono w h
    have : (0 : ℝ) ≤ 1 / 3 ^ r := by positivity
    linarith
  · have := hi_anti w h
    have : (0 : ℝ) < 1 / 3 ^ s := by positivity
    linarith

lemma bdd_lo (w : ℕ → CommGraph) : BddAbove (Set.range (lo w)) :=
  ⟨lo w 0 + 1 / 3 ^ 0, by rintro _ ⟨s, rfl⟩; exact lo_le_hi w s 0⟩

lemma piMap_mem (w : ℕ → CommGraph) (r : ℕ) :
    lo w r ≤ piMap w ∧ piMap w ≤ lo w r + 1 / 3 ^ r :=
  ⟨le_ciSup (bdd_lo w) r, ciSup_le (fun s => lo_le_hi w s r)⟩

lemma extend_graphs (h : List CommGraph) : ∃ w : ℕ → CommGraph, pre w h.length = h := by
  refine ⟨fun i => h.getD i .both, ?_⟩
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2; simp [pre]

lemma inj_pre : ∀ (m : ℕ) (w w' : ℕ → CommGraph),
    jIdx (pre w m) = jIdx (pre w' m) → pre w m = pre w' m
  | 0, _, _, _ => by simp [pre]
  | m + 1, w, w', h => by
      rw [pre_succ_gen, pre_succ_gen] at h ⊢
      rw [jIdx_append, jIdx_append] at h
      have b1 := stepJ_bounds (jIdx (pre w m)) (w m)
      have b2 := stepJ_bounds (jIdx (pre w' m)) (w' m)
      have ha : jIdx (pre w m) = jIdx (pre w' m) := by omega
      have hp := inj_pre m w w' ha
      rw [hp]
      congr 2
      rw [ha] at h
      apply delta_inj
      have d1 := delta_le (w m)
      have d2 := delta_le (w' m)
      unfold stepJ at h
      split at h <;> omega

lemma inj_list (g g' : List CommGraph) (hl : g.length = g'.length) (h : jIdx g = jIdx g') :
    g = g' := by
  obtain ⟨w, hw⟩ := extend_graphs g
  obtain ⟨w', hw'⟩ := extend_graphs g'
  rw [← hl] at hw'
  rw [← hw, ← hw'] at h ⊢
  exact inj_pre _ w w' h

lemma idx_eq (a b m : ℕ) (t : ℝ)
    (h1 : (a : ℝ) / 3 ^ m ≤ t) (h2 : t ≤ (a : ℝ) / 3 ^ m + 1 / 3 ^ m)
    (h3 : (b : ℝ) / 3 ^ m < t) (h4 : t < (b : ℝ) / 3 ^ m + 1 / 3 ^ m) : a = b := by
  have hp : (0 : ℝ) < 3 ^ m := by positivity
  have e1 : (a : ℝ) / 3 ^ m + 1 / 3 ^ m = ((a : ℝ) + 1) / 3 ^ m := by ring
  have e2 : (b : ℝ) / 3 ^ m + 1 / 3 ^ m = ((b : ℝ) + 1) / 3 ^ m := by ring
  rw [e1] at h2; rw [e2] at h4
  rw [div_le_iff₀ hp] at h1; rw [le_div_iff₀ hp] at h2
  rw [div_lt_iff₀ hp] at h3; rw [lt_div_iff₀ hp] at h4
  have hab : (a : ℝ) < b + 1 := by linarith
  have hba : (b : ℝ) < a + 1 := by linarith
  have : a < b + 1 := by exact_mod_cast hab
  have : b < a + 1 := by exact_mod_cast hba
  omega

lemma closure_ne_Icc_of_missing (B : Set (ℕ → CommGraph)) (k : List CommGraph)
    (hk : k ∉ Pref B) : closure (piMap '' B) ≠ Set.Icc (0 : ℝ) 1 := by
  intro hcl
  set m := k.length
  set δ : ℝ := 1 / (3 : ℝ) ^ m / 2
  have hδ : 0 < δ := by positivity
  set c : ℝ := (jIdx k : ℝ) / (3 : ℝ) ^ m + δ
  have hlt : jIdx k < 3 ^ m := jIdx_lt k
  have hp : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hc_mem : c ∈ Set.Icc (0 : ℝ) 1 := by
    have h0 : 0 ≤ (jIdx k : ℝ) / (3 : ℝ) ^ m := by positivity
    have hle1 : (jIdx k : ℝ) + 1 ≤ (3 : ℝ) ^ m := by
      have : jIdx k + 1 ≤ 3 ^ m := by omega
      exact_mod_cast this
    have hc_hi : c ≤ ((jIdx k : ℝ) + 1) / (3 : ℝ) ^ m := by
      simp only [c, δ]
      have hpos_inv : 0 < (1 : ℝ) / (3 : ℝ) ^ m := by positivity
      have : (jIdx k : ℝ) / (3 : ℝ) ^ m + 1 / (3 : ℝ) ^ m / 2 ≤
          (jIdx k : ℝ) / (3 : ℝ) ^ m + 1 / (3 : ℝ) ^ m := by linarith
      linarith [show (jIdx k : ℝ) / (3 : ℝ) ^ m + 1 / (3 : ℝ) ^ m =
          ((jIdx k : ℝ) + 1) / (3 : ℝ) ^ m by ring]
    have hdiv1 : ((jIdx k : ℝ) + 1) / (3 : ℝ) ^ m ≤ 1 := (div_le_one hp).mpr hle1
    exact ⟨by linarith, by linarith⟩
  rw [← hcl, Metric.mem_closure_iff] at hc_mem
  obtain ⟨y, ⟨w, hwB, rfl⟩, hdist⟩ := hc_mem δ hδ
  rw [Real.dist_eq, abs_lt] at hdist
  have hm := piMap_mem w m
  unfold lo at hm
  have heq : jIdx (pre w m) = jIdx k := by
    apply idx_eq (jIdx (pre w m)) (jIdx k) m (piMap w) hm.1 hm.2
    · simp only [c] at hdist; linarith [hdist.1]
    · simp only [c, δ] at hdist
      have : 1 / (3 : ℝ) ^ m / 2 + 1 / (3 : ℝ) ^ m / 2 = 1 / (3 : ℝ) ^ m := by ring
      linarith [hdist.2]
  exact hk ⟨w, hwB, inj_list (pre w m) k (pre_length_gen w m) heq⟩

lemma pre_append_eq {α : Type} (u : List α) (w : ℕ → α) :
    pre (append u w) u.length = u := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2; simp [pre, append]

lemma eq_append_of_pre {α : Type} (w : ℕ → α) (u : List α) (h : pre w u.length = u) :
    w = append u (fun n => w (u.length + n)) := by
  funext n
  unfold append
  split_ifs with hn
  · have hget := congrArg (fun l => l[n]?) h
    simpa [pre, hn] using hget
  · congr 1
    omega

lemma append_append_eq {α : Type} (h k : List α) (w : ℕ → α) :
    append h (append k w) = append (h ++ k) w := by
  funext n
  simp only [append, List.length_append]
  by_cases hn : n < h.length
  · have hn2 : n < h.length + k.length := by omega
    simp [hn, hn2, List.getElem_append_left hn]
  · by_cases hk : n - h.length < k.length
    · have hn2 : n < h.length + k.length := by omega
      simp [hn, hk, hn2, List.getElem_append_right (Nat.le_of_not_lt hn)]
    · have hn2 : ¬ (n < h.length + k.length) := by omega
      simp [hn, hk, hn2]
      congr 1
      omega

lemma not_mem_pref_leftQuot {α : Type} (A : Set (ℕ → α)) (h k : List α)
    (hmiss : h ++ k ∉ Pref A) : k ∉ Pref (leftQuot h A) := by
  rintro ⟨w, hw, hpre⟩
  apply hmiss
  have hw_eq := eq_append_of_pre w k hpre
  change append h w ∈ A at hw
  rw [hw_eq, append_append_eq] at hw
  exact ⟨append (h ++ k) (fun n => w (k.length + n)), hw, pre_append_eq (h ++ k) _⟩

/-! ### Encoding a finite-state DPA into `DPACode` -/

def idxInv : ℕ → CommGraph
  | 0 => .oneToTwo
  | 1 => .both
  | _ => .twoToOne

lemma idx_lt_three (g : CommGraph) : g.idx < 3 := by
  cases g <;> decide

lemma idxInv_idx (g : CommGraph) : idxInv g.idx = g := by
  cases g <;> rfl

lemma exists_dpaCode {S : Type} [Fintype S] (M : DPA S CommGraph) :
    ∃ c : DPACode, c.lang = M.lang := by
  classical
  have hneS : Nonempty S := ⟨M.init⟩
  have hpos : 0 < Fintype.card S := @Fintype.card_pos S _ hneS
  let n : ℕ := Fintype.card S - 1
  have hn : Fintype.card S = n + 1 := by omega
  let e0 : S ≃ Fin (n + 1) := (Fintype.equivFin S).trans (finCongr hn)
  let z : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let e : S ≃ Fin (n + 1) := e0.trans (Equiv.swap (e0 M.init) z)
  have he_init : e M.init = z := by simp [e]
  let trans : List ℕ := (List.range (3 * (n + 1))).map fun k =>
    if hk : k / 3 < n + 1 then (e (M.step (e.symm ⟨k / 3, hk⟩) (idxInv (k % 3)))).val else 0
  let prios : List ℕ := (List.finRange (n + 1)).map fun i => M.prio (e.symm i)
  let c : DPACode := (n, trans, prios)
  refine ⟨c, ?_⟩
  have hstep : ∀ (q : S) (g : CommGraph), c.toDPA.step (e q) g = e (M.step q g) := by
    intro q g
    apply Fin.ext
    simp only [DPACode.toDPA, c]
    have hg : g.idx < 3 := idx_lt_three g
    have hq : (e q).val < n + 1 := (e q).isLt
    let k := 3 * (e q).val + g.idx
    have hk_lt : k < 3 * (n + 1) := by omega
    have hk_div : k / 3 = (e q).val := by omega
    have hk_mod : k % 3 = g.idx := by omega
    have hget : trans.getD k 0 = (e (M.step q g)).val := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [trans, hk_lt]), Option.getD_some]
      simp only [trans, List.getElem_map, List.getElem_range]
      rw [dif_pos (by omega)]
      have hfin : (⟨k / 3, by omega⟩ : Fin (n + 1)) = e q := Fin.ext hk_div
      rw [hfin, Equiv.symm_apply_apply, hk_mod, idxInv_idx]
    change (trans.getD k 0) % (n + 1) = (e (M.step q g)).val
    rw [hget, Nat.mod_eq_of_lt (e (M.step q g)).isLt]
  have hrun : ∀ (w : ℕ → CommGraph) (t : ℕ), c.toDPA.run w t = e (M.run w t) := by
    intro w t
    induction t with
    | zero => exact he_init.symm
    | succ t ih => simp only [DPA.run, ih, hstep]
  have hprio : ∀ q : S, c.toDPA.prio (e q) = M.prio q := by
    intro q
    let idx : Fin (n + 1) := e q
    change prios.getD idx.val 0 = M.prio q
    have hq : idx.val < prios.length := by
      simp only [prios, List.length_map, List.length_finRange]
      exact idx.isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    have hget : prios[idx.val] = M.prio (e.symm idx) := by
      simp only [prios, List.getElem_map, List.getElem_finRange]
      congr 2
    rw [hget]
    exact congrArg M.prio (e.symm_apply_apply q)
  ext w
  change c.toDPA.Accepts w ↔ M.Accepts w
  unfold DPA.Accepts
  have hseq : (fun t => c.toDPA.prio (c.toDPA.run w t)) = (fun t => M.prio (M.run w t)) := by
    funext t
    rw [hrun, hprio]
  rw [hseq]

end DistLTLSynth.Char.Lemma32Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma32Aux in
theorem solution (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (A : Set (ℕ → CommGraph)) :
    (RepeatedlySolvableBounded V A ↔ IsNowhereDense (piMap '' A)) ∧
      (IsNowhereDense (piMap '' A) →
        ∀ (S : Type) [Fintype S] (M : DPA S CommGraph), M.lang = A →
          RepeatedlySolvableUniform V A) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Part 1 (`→`): contrapositive via `lemma_6_16` and `lemma_5_2`
    intro hrep
    by_contra hnot
    obtain ⟨h, hdense⟩ := lemma_6_16 A hnot
    have : Nonempty (ℕ → CommGraph) := ⟨fun _ => .both⟩
    obtain ⟨w, hw⟩ := hdense.nonempty
    have hh_pref : h ∈ Pref A := ⟨append h w, hw, pre_append_eq h w⟩
    have hnot_cl : closure (piMap '' leftQuot h A) ≠ Set.Icc (0 : ℝ) 1 :=
      (lemma_5_2 V hV (leftQuot h A)).mp (hrep h hh_pref)
    apply hnot_cl
    apply Set.Subset.antisymm
    · apply closure_minimal _ isClosed_Icc
      rintro _ ⟨u, -, rfl⟩
      rw [← lemma_2_4.2]
      exact ⟨u, rfl⟩
    · calc
        Set.Icc (0 : ℝ) 1 = Set.range piMap := lemma_2_4.2.symm
        _ = piMap '' Set.univ := Set.image_univ.symm
        _ = piMap '' closure (leftQuot h A) := by rw [hdense.closure_eq]
        _ ⊆ closure (piMap '' leftQuot h A) := image_closure_subset_closure_image lemma_2_4.1
  · -- Part 1 (`←`): `lemma_6_15` + `lemma_5_2`
    intro hND h _
    obtain ⟨k, hk_miss⟩ := (lemma_6_15 A).mp hND h
    have hk_quot : k ∉ Pref (leftQuot h A) := not_mem_pref_leftQuot A h k hk_miss
    exact (lemma_5_2 V hV (leftQuot h A)).mpr (closure_ne_Icc_of_missing (leftQuot h A) k hk_quot)
  · -- Part 2: encode `M` as `DPACode` and apply `lemma_3_6`
    intro hND S _ M hM
    obtain ⟨c, hc_lang⟩ := exists_dpaCode M
    have hcA : c.lang = A := hc_lang.trans hM
    obtain ⟨D, _, hDc⟩ := lemma_3_6 V hV
    rw [← hcA] at hND ⊢
    exact ⟨D c, (hDc c hND).2⟩
