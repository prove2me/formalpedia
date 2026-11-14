-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.merge_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:11:07.352452+00:00
-- url     : https://prove2.me/submissions/d9793547-daa3-4af1-b5c1-8eaabf9c5851

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_Hp_vs
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_VS_append_free
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_VS_of_pairs
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_complete_sol_pre
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_noOver_pre
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_walkB_spec
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_completeSeq_validSeq
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_sol_sol
public import Theorems.Thm_BCFGJPSSV26_Greedy_ValidSeq_param_f
public import Theorems.Thm_BCFGJPSSV26_Greedy_ValidSeq_param_u

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

/-- A **good output** from a valid sequence with count `k` after a good prefix. -/
theorem goodOut_of {p b : ℕ} {pre : List (List AAtom)} (hpre : PreOK hX p b pre)
    {W : List AAtom} (hW : MergeH.VS hX p b pre W) (hok : ∀ a ∈ W, C.AtomOK a)
    (hfree : nFreeSeqA W ≤ 3) (hk : C.cnt (C.fhat b) pre W = C.ip.k) :
    GoodOut hX (C.complete (C.fhat b) (pre ++ [W])) b := by
  obtain ⟨hsol, hok'⟩ :=
    MergeH.complete_sol_pre hX hpre.len hpre.lt hpre.b_le hpre.valid hpre.ok hW hok
  have hk' : nRegA (C.complete (C.fhat b) (pre ++ [W])) = C.ip.k := hk
  exact ⟨hsol, hok', hpre.b_le, PreOK.free_complete hX hpre _ hfree, .inl hk',
    hk' ▸ hX.one_le_k⟩

/-- The **promise** from two free copies of `z` at adjacent offsets after a valid `base`. -/
theorem promise_of {p b : ℕ} {pre : List (List AAtom)} (hpre : PreOK hX p b pre)
    {base : List AAtom} (hbase : MergeH.VS hX p b pre base) (hok : ∀ a ∈ base, C.AtomOK a)
    (hfree : nFreeSeqA base ≤ 2) {z g : ℕ} (hz : z < C.ip.m) (hg : g + 1 ≤ 2 ^ C.ip.Pu)
    (hs : sandwich (C.cnt (C.fhat b) pre (base ++ [(z, g + 1)]))
      (C.cnt (C.fhat b) pre (base ++ [(z, g + 1 + 1)])) C.ip.k = true) :
    Promise hX (p + 1) ⟨C.complete (C.fhat b) (pre ++ [base ++ [(z, g + 1)]]),
      C.complete (C.fhat b) (pre ++ [base ++ [(z, g + 1 + 1)]]), b, b⟩ := by
  have hv1 := MergeH.VS.append_free hX hpre.len hpre.valid hbase z g
  have hv2 := MergeH.VS.append_free hX hpre.len hpre.valid hbase z (g + 1)
  have hok1 : ∀ a ∈ base ++ [(z, g + 1)], C.AtomOK a := fun a ha ↦ by
    rcases List.mem_append.1 ha with ha | ha
    · exact hok a ha
    · rw [List.mem_singleton.1 ha]
      exact atomOK_free hz (by omega)
  have hok2 : ∀ a ∈ base ++ [(z, g + 1 + 1)], C.AtomOK a := fun a ha ↦ by
    rcases List.mem_append.1 ha with ha | ha
    · exact hok a ha
    · rw [List.mem_singleton.1 ha]
      exact atomOK_free hz hg
  obtain ⟨hs1, ho1⟩ :=
    MergeH.complete_sol_pre hX hpre.len hpre.lt hpre.b_le hpre.valid hpre.ok hv1 hok1
  obtain ⟨hs2, ho2⟩ :=
    MergeH.complete_sol_pre hX hpre.len hpre.lt hpre.b_le hpre.valid hpre.ok hv2 hok2
  have hf1 : nFreeSeqA (base ++ [(z, g + 1)]) ≤ 3 := by
    rw [MergeH.nFreeSeqA_append, MergeH.nFreeSeqA_free]
    omega
  have hf2 : nFreeSeqA (base ++ [(z, g + 1 + 1)]) ≤ 3 := by
    rw [MergeH.nFreeSeqA_append, MergeH.nFreeSeqA_free]
    omega
  refine ⟨hs1, hs2, ho1, ho2, hpre.b_le, hpre.b_le, hs,
    .inr ⟨rfl, p, Nat.lt_succ_self p, base.length, z, g, hg, ?_, ?_⟩, ?_, ?_,
    fun q ↦ ⟨PreOK.free_complete hX hpre _ hf1 q, PreOK.free_complete hX hpre _ hf2 q⟩⟩
  · dsimp only
    rw [MergeH.complete_getD_self hpre.len hpre.lt, MergeH.getD_append_self]
  · dsimp only
    rw [MergeH.complete_take_succ hpre.len hpre.lt, MergeH.complete_take_succ hpre.len hpre.lt,
      ← hpre.len, MergeH.modify_last]
    simp
  · dsimp only
    rw [MergeH.complete_take_succ hpre.len hpre.lt]
  · dsimp only
    rw [MergeH.complete_take_succ hpre.len hpre.lt]

/-- **The offset search** (BinSearch) after a valid `base` with at most two free atoms, when the
counts with a free copy of `z` at offset `0` and without it sandwich `k` (or the first is `k`). -/
theorem binSearch_spec {p b : ℕ} {pre : List (List AAtom)} (hpre : PreOK hX p b pre)
    {base : List AAtom} (hbase : ValidSeq C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten)
      (decS hX base)) (hok : ∀ a ∈ base, C.AtomOK a) (hfree : nFreeSeqA base ≤ 2) {z : ℕ}
    (hz : z < C.ip.m)
    (hs : C.cnt (C.fhat b) pre (base ++ [(z, 1)]) = C.ip.k ∨
      sandwich (C.cnt (C.fhat b) pre (base ++ [(z, 1)])) (C.cnt (C.fhat b) pre base) C.ip.k) :
    (∃ H, C.binSearch (C.fhat b) b pre base z = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr', C.binSearch (C.fhat b) b pre base z = .cont pr' ∧ Promise hX (p + 1) pr') := by
  have hdone : ∀ g, g ≤ 2 ^ C.ip.Pu → C.cnt (C.fhat b) pre (base ++ [(z, g + 1)]) = C.ip.k →
      GoodOut hX (C.complete (C.fhat b) (pre ++ [base ++ [(z, g + 1)]])) b := by
    intro g hg hk
    refine goodOut_of hX hpre (MergeH.VS.append_free hX hpre.len hpre.valid hbase z g)
      (fun a ha ↦ ?_) ?_ hk
    · rcases List.mem_append.1 ha with ha | ha
      · exact hok a ha
      · rw [List.mem_singleton.1 ha]
        exact atomOK_free hz hg
    · rw [MergeH.nFreeSeqA_append, MergeH.nFreeSeqA_free]
      omega
  simp only [binSearch]
  by_cases h0 : C.cnt (C.fhat b) pre (base ++ [(z, 0 + 1)]) = C.ip.k
  · rw [if_pos h0]
    exact .inl ⟨_, rfl, hdone 0 (Nat.zero_le _) h0⟩
  rw [if_neg h0]
  by_cases hK : C.cnt (C.fhat b) pre (base ++ [(z, 2 ^ C.ip.Pu + 1)]) = C.ip.k
  · rw [if_pos hK]
    exact .inl ⟨_, rfl, hdone _ le_rfl hK⟩
  rw [if_neg hK]
  have hs' : sandwich (C.cnt (C.fhat b) pre (base ++ [(z, 0 + 1)]))
      (C.cnt (C.fhat b) pre (base ++ [(z, 2 ^ C.ip.Pu + 1)])) C.ip.k = true := by
    rw [cnt_append_top hX]
    rcases hs with hs | hs
    · exact absurd hs h0
    · exact hs
  rcases searchStep_spec (c := fun g ↦ C.cnt (C.fhat b) pre (base ++ [(z, g + 1)]))
    (P := C.ip.Pu) hs' with ⟨lo, heq, hlo, hsand, -⟩ | ⟨lo, hi, g, heq, hg, hgle⟩
  · rw [heq]
    exact .inr ⟨_, rfl, promise_of hX hpre hbase hok hfree hz hlo hsand⟩
  · rw [heq]
    exact .inl ⟨_, rfl, hdone g hgle hg⟩

/-- **Step C** between `before = X ++ h? ++ Y` and `after = X ++ Y ++ Z`, two valid sequences
after a good prefix whose counts sandwich `k`, where `Z` has only regular atoms and `X ++ Y` at
most one free atom. -/
theorem stepC_spec {p b : ℕ} {pre : List (List AAtom)} (hpre : PreOK hX p b pre)
    {Xs Y Z : List AAtom} {h : Option AAtom}
    (hbefore : ValidSeq C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten)
      (decS hX (Xs ++ h.toList ++ Y)))
    (hafter : ValidSeq C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten)
      (decS hX (Xs ++ Y ++ Z)))
    (hok : ∀ a ∈ Xs ++ h.toList ++ Y ++ Z, C.AtomOK a) (hZ : ∀ a ∈ Z, a.2 = 0)
    (hh : ∀ a ∈ h.toList, a.2 = 0) (hfree : nFreeSeqA (Xs ++ Y) ≤ 1)
    (hs : sandwich (C.cnt (C.fhat b) pre (Xs ++ h.toList ++ Y))
      (C.cnt (C.fhat b) pre (Xs ++ Y ++ Z)) C.ip.k = true) (dflt : Res) :
    (∃ H, C.stepC (C.fhat b) b pre Xs h Y Z dflt = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr', C.stepC (C.fhat b) b pre Xs h Y Z dflt = .cont pr' ∧ Promise hX (p + 1) pr') := by
  have hokXY : ∀ a ∈ Xs ++ Y, C.AtomOK a := fun a ha ↦ hok a (by
    simp only [List.mem_append] at ha ⊢
    tauto)
  have hokZ : ∀ a ∈ Z, C.AtomOK a := fun a ha ↦ hok a (by simp [ha])
  have hokh : ∀ a ∈ h.toList, C.AtomOK a := fun a ha ↦ hok a (by simp [ha])
  -- the free copies of `h` at offset `0`
  obtain ⟨F, hF⟩ : ∃ F : List AAtom, F = h.toList.map fun a ↦ ((a.1, 1) : AAtom) := ⟨_, rfl⟩
  have hFfree : ∀ a ∈ F, a.2 = 1 := by
    intro a ha
    rw [hF] at ha
    obtain ⟨a', -, rfl⟩ := List.mem_map.1 ha
    rfl
  have hFok : ∀ a ∈ F, C.AtomOK a := by
    intro a ha
    rw [hF] at ha
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    exact atomOK_free (g := 0) (hokh a' ha').1 (Nat.zero_le _)
  have hFn : nFreeSeqA F ≤ 1 := by
    have h1 := MergeH.nFreeSeqA_le_length F
    have h2 : F.length ≤ 1 := by
      rw [hF, List.length_map]
      cases h <;> simp
    omega
  -- the points `Xs ++ Y ++ Z.drop r ++ F`
  have hpairs : ∀ r, pairs (decS hX pre.flatten ++ decS hX (Xs ++ h.toList ++ Y)) ⊆
      pairs (decS hX pre.flatten ++ decS hX (Xs ++ Y ++ Z.drop r ++ F)) := by
    intro r
    refine MergeH.pairs_subset_of hX (fun a ha ↦ ?_) _
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact ⟨a, by simp [ha], rfl⟩
    · refine ⟨(a.1, 1), List.mem_append_right _ (by rw [hF]; exact List.mem_map.2 ⟨a, ha, rfl⟩),
        ?_⟩
      rw [MergeH.decA_pair_one]
      rw [show a = (a.1, 0) from Prod.ext rfl (hh a ha)]
    · exact ⟨a, by simp [ha], rfl⟩
  have hPt : ∀ r, MergeH.VS hX p b pre (Xs ++ Y ++ Z.drop r ++ F) ∧
      (∀ a ∈ Xs ++ Y ++ Z.drop r ++ F, C.AtomOK a) ∧
      nFreeSeqA (Xs ++ Y ++ Z.drop r ++ F) ≤ 2 := by
    intro r
    refine ⟨MergeH.VS.of_pairs hX hpre.len hpre.valid hbefore ?_ (hpairs r), fun a ha ↦ ?_, ?_⟩
    · have h1 := hafter.1
      rw [show Xs ++ Y ++ Z = Xs ++ Y ++ Z.take r ++ Z.drop r by simp, decS_append,
        decS_append] at h1
      rw [decS_append, decS_append]
      exact MergeH.atomsValid_append.2 ⟨MergeH.AtomsValid.delete h1,
        MergeH.atomsValid_of_free fun a ha ↦ by
          obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
          rw [MergeH.decA_free_eq, hFfree a' ha']
          rfl⟩
    · simp only [List.mem_append] at ha
      rcases ha with ((ha | ha) | ha) | ha
      · exact hokXY a (by simp [ha])
      · exact hokXY a (by simp [ha])
      · exact hokZ a (List.mem_of_mem_drop ha)
      · exact hFok a ha
    · rw [MergeH.nFreeSeqA_append, MergeH.nFreeSeqA_append,
        MergeH.nFreeSeqA_eq_zero fun a ha ↦ hZ a (List.mem_of_mem_drop ha)]
      omega
  have hokA : ∀ a ∈ Xs ++ Y ++ Z, C.AtomOK a := fun a ha ↦ by
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact hokXY a (by simp [ha])
    · exact hokXY a (by simp [ha])
    · exact hokZ a ha
  have hfA : nFreeSeqA (Xs ++ Y ++ Z) ≤ 1 := by
    rw [MergeH.nFreeSeqA_append, MergeH.nFreeSeqA_eq_zero hZ]
    omega
  -- the counts
  have hcB : C.cnt (C.fhat b) pre (Xs ++ h.toList ++ Y) =
      C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop Z.length ++ F) + h.toList.length := by
    rw [List.drop_length, List.append_nil]
    cases h with
    | none => simp [hF]
    | some h₀ =>
      have e : h₀ = (h₀.1, 0) := Prod.ext rfl (hh h₀ (by simp))
      simp only [Option.toList, List.length_singleton, hF, List.map_cons, List.map_nil]
      rw [e, List.append_assoc, List.singleton_append, MergeH.cnt_swapFree']
  have hcR : ∀ t < Z.length, C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop t ++ F) =
      C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop (t + 1) ++ F ++ [((Z.getD t (0, 0)).1, 1)]) + 1 := by
    intro t ht
    obtain ⟨z, hz⟩ : ∃ z, (Z.getD t (0, 0)).1 = z := ⟨_, rfl⟩
    have e : Z[t] = (z, 0) :=
      Prod.ext (by rw [← hz, MergeH.getD_of_lt ht]) (hZ _ (List.getElem_mem ht))
    rw [hz, List.drop_eq_getElem_cons ht, e]
    have := MergeH.cnt_swapFree' (C := C) (C.fhat b) pre (Xs ++ Y) (Z.drop (t + 1) ++ F) z
    simpa only [List.append_assoc, List.cons_append] using this
  -- the leaves
  have hfind : ∀ W ∈ (Xs ++ Y ++ Z) :: (List.range (Z.length + 1)).map
      (fun r ↦ Xs ++ Y ++ Z.drop r ++ F), C.cnt (C.fhat b) pre W = C.ip.k →
      GoodOut hX (C.complete (C.fhat b) (pre ++ [W])) b := by
    intro W hW hk
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hW
    rcases hW with rfl | ⟨r, -, rfl⟩
    · exact goodOut_of hX hpre hafter hokA (by omega) hk
    · exact goodOut_of hX hpre (hPt r).1 (hPt r).2.1 (by have := (hPt r).2.2; omega) hk
  have hflip : ∀ t < Z.length, sandwich (C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop t ++ F))
      (C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop (t + 1) ++ F)) C.ip.k = true →
      (∃ H, (if C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop (t + 1) ++ F ++
          [((Z.getD t (0, 0)).1, 1)]) = C.ip.k then
          Res.done (C.complete (C.fhat b) (pre ++ [Xs ++ Y ++ Z.drop (t + 1) ++ F ++
            [((Z.getD t (0, 0)).1, 1)]])) b
        else C.binSearch (C.fhat b) b pre (Xs ++ Y ++ Z.drop (t + 1) ++ F)
          (Z.getD t (0, 0)).1) = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr', (if C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop (t + 1) ++ F ++
          [((Z.getD t (0, 0)).1, 1)]) = C.ip.k then
          Res.done (C.complete (C.fhat b) (pre ++ [Xs ++ Y ++ Z.drop (t + 1) ++ F ++
            [((Z.getD t (0, 0)).1, 1)]])) b
        else C.binSearch (C.fhat b) b pre (Xs ++ Y ++ Z.drop (t + 1) ++ F)
          (Z.getD t (0, 0)).1) = .cont pr' ∧ Promise hX (p + 1) pr') := by
    intro t ht hst
    have hz : (Z.getD t (0, 0)).1 < C.ip.m := by
      rw [MergeH.getD_of_lt ht]
      exact (hokZ _ (List.getElem_mem ht)).1
    obtain ⟨hv, hokP, hfP⟩ := hPt (t + 1)
    by_cases hk : C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop (t + 1) ++ F ++
        [((Z.getD t (0, 0)).1, 1)]) = C.ip.k
    · rw [if_pos hk]
      refine .inl ⟨_, rfl, goodOut_of hX hpre (hv.append_free hX hpre.len hpre.valid _ 0)
        (fun a ha ↦ ?_) ?_ hk⟩
      · rcases List.mem_append.1 ha with ha | ha
        · exact hokP a ha
        · rw [List.mem_singleton.1 ha]
          exact atomOK_free hz (Nat.zero_le _)
      · rw [MergeH.nFreeSeqA_append, MergeH.nFreeSeqA_free]
        omega
    · rw [if_neg hk]
      refine binSearch_spec hX hpre hv hokP hfP hz (.inr ?_)
      have h1 := hcR t ht
      rw [MergeH.sandwich_iff] at hst ⊢
      omega
  have hnone : (∀ W ∈ (Xs ++ Y ++ Z) :: (List.range (Z.length + 1)).map
      (fun r ↦ Xs ++ Y ++ Z.drop r ++ F), C.cnt (C.fhat b) pre W ≠ C.ip.k) →
      firstFlip C.ip.k (((Xs ++ Y ++ Z) :: (List.range (Z.length + 1)).map
        (fun r ↦ Xs ++ Y ++ Z.drop r ++ F)).map (C.cnt (C.fhat b) pre)) = none → False := by
    intro hne hff
    have h1 := MergeH.firstFlip_none' hff (fun x hx ↦ by
      obtain ⟨W, hW, rfl⟩ := List.mem_map.1 hx
      exact hne W hW) (Z.length + 1) (by rw [MergeH.length_cnts]; omega)
    rw [MergeH.getD_cnts_succ _ _ _ le_rfl, MergeH.getD_cnts_zero, decide_eq_decide] at h1
    have h2 := hne _ (List.mem_cons_self ..)
    have h3 := hne (Xs ++ Y ++ Z.drop Z.length ++ F) (List.mem_cons_of_mem _
      (List.mem_map.2 ⟨Z.length, List.mem_range.2 (by omega), rfl⟩))
    have h4 : h.toList.length ≤ 1 := by cases h <;> simp
    rw [MergeH.sandwich_iff, hcB] at hs
    by_cases h5 : C.cnt (C.fhat b) pre (Xs ++ Y ++ Z.drop Z.length ++ F) < C.ip.k
    · have := h1.1 h5
      omega
    · have : ¬ C.cnt (C.fhat b) pre (Xs ++ Y ++ Z) < C.ip.k := fun h6 ↦ h5 (h1.2 h6)
      omega
  -- the dispatch
  cases h with
  | none =>
    simp only [Option.toList, List.map_nil] at hF
    subst hF
    simp only [stepC]
    split
    next W hW =>
      exact .inl ⟨_, rfl, hfind W (List.mem_of_find?_eq_some hW)
        (by simpa using List.find?_some hW)⟩
    next hW =>
      have hne := List.find?_eq_none.1 hW
      have hne' : ∀ W ∈ (Xs ++ Y ++ Z) :: (List.range (Z.length + 1)).map
          (fun r ↦ Xs ++ Y ++ Z.drop r ++ []), C.cnt (C.fhat b) pre W ≠ C.ip.k :=
        fun W hW' hk ↦ hne W hW' (decide_eq_true hk)
      split
      next hff =>
        exfalso
        have h1 := (MergeH.firstFlip_some' hff).2
        rw [MergeH.getD_cnts_zero, MergeH.getD_cnts_succ _ _ _ (Nat.zero_le _)] at h1
        simp [MergeH.sandwich_iff] at h1
        omega
      next t hff =>
        obtain ⟨h1, h2⟩ := MergeH.firstFlip_some' hff
        rw [MergeH.length_cnts] at h1
        rw [MergeH.getD_cnts_succ _ _ _ (by omega), MergeH.getD_cnts_succ _ _ _ (by omega)] at h2
        exact hflip t (by omega) h2
      next hff => exact (hnone hne' hff).elim
  | some h₀ =>
    simp only [Option.toList, List.map_cons, List.map_nil] at hF
    subst hF
    simp only [stepC]
    split
    next W hW =>
      exact .inl ⟨_, rfl, hfind W (List.mem_of_find?_eq_some hW)
        (by simpa using List.find?_some hW)⟩
    next hW =>
      have hne := List.find?_eq_none.1 hW
      have hne' : ∀ W ∈ (Xs ++ Y ++ Z) :: (List.range (Z.length + 1)).map
          (fun r ↦ Xs ++ Y ++ Z.drop r ++ [(h₀.1, 1)]), C.cnt (C.fhat b) pre W ≠ C.ip.k :=
        fun W hW' hk ↦ hne W hW' (decide_eq_true hk)
      split
      next hff =>
        have h1 := (MergeH.firstFlip_some' hff).2
        rw [MergeH.getD_cnts_zero, MergeH.getD_cnts_succ _ _ _ (Nat.zero_le _)] at h1
        simp only [List.drop_zero] at h1
        refine binSearch_spec hX hpre hafter hokA (by omega) (hokh h₀ (by simp)).1 (.inr ?_)
        rwa [MergeH.sandwich_comm] at h1
      next t hff =>
        obtain ⟨h1, h2⟩ := MergeH.firstFlip_some' hff
        rw [MergeH.length_cnts] at h1
        rw [MergeH.getD_cnts_succ _ _ _ (by omega), MergeH.getD_cnts_succ _ _ _ (by omega)] at h2
        exact hflip t (by omega) h2
      next hff => exact (hnone hne' hff).elim

/-- **Step B**: the walk from a valid sequence `H'p` (regular atoms only) to the sequence `Hp` of
the dominant solution, when their counts sandwich `k`. Every point of the walk is a valid
sequence with at most one free atom; consecutive counts differ by a free atom, a deletion with
completion, or a free copy made regular (which raises the count by exactly one, so it is never
the flip); the walk ends with `Hp` as a prefix. -/
theorem walkPhase_spec {p b : ℕ} {pre : List (List AAtom)} (hpre : PreOK hX p b pre)
    {Hp H'p : List AAtom}
    (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])
    (hH'p : ValidSeq C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten) (decS hX H'p))
    (hok : ∀ a ∈ H'p, C.AtomOK a) (hreg : ∀ a ∈ H'p, a.2 = 0)
    (hs : sandwich (C.cnt (C.fhat b) pre H'p) (C.cnt (C.fhat b) pre Hp) C.ip.k = true)
    (dflt : Res) :
    (∃ H, C.walkPhase p (C.fhat b) b pre Hp H'p dflt = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr', C.walkPhase p (C.fhat b) b pre Hp H'p dflt = .cont pr' ∧
        Promise hX (p + 1) pr') := by
  obtain ⟨hinv, cur, κ, hlast, hpref, hcreg⟩ :=
    MergeH.walkB_spec hX hpre.len hpre.valid hpre.ok hHp hH'p hok hreg
  simp only [walkPhase]
  generalize C.walkB p (C.fhat b) pre Hp H'p = pts at hinv hlast ⊢
  have hlen : 0 < pts.length := List.length_pos_of_ne_nil (by rintro rfl; simp at hlast)
  split
  next w hw =>
    obtain ⟨h1, h2, h3⟩ := hinv.pt w (List.mem_of_find?_eq_some hw)
    exact .inl ⟨_, rfl, goodOut_of hX hpre h1 h2 (by omega) (by simpa using List.find?_some hw)⟩
  next hw =>
    have hne : ∀ w ∈ pts, C.cnt (C.fhat b) pre w.1 ≠ C.ip.k :=
      fun w hw' hk ↦ List.find?_eq_none.1 hw w hw' (by simpa using hk)
    split
    next t hff =>
      obtain ⟨ht, hsand⟩ := firstFlip_some hff
      rw [List.length_map] at ht
      have ht' : t < pts.length := by omega
      rw [MergeH.getD_of_lt (by rw [List.length_map]; exact ht'),
        MergeH.getD_of_lt (by rw [List.length_map]; exact ht), List.getElem_map,
        List.getElem_map] at hsand
      have htr := hinv.tr t ht
      have hpt0 := hinv.pt _ (List.getElem_mem ht')
      have hpt1 := hinv.pt _ (List.getElem_mem ht)
      rw [MergeH.getD_of_lt ht, MergeH.getD_of_lt ht']
      generalize pts[t] = w0 at htr hsand hpt0 ⊢
      generalize pts[t + 1] = w1 at htr hsand hpt1 ⊢
      obtain ⟨S, κ0⟩ := w0
      obtain ⟨W, κ1⟩ := w1
      dsimp only at htr hsand hpt0 hpt1 ⊢
      cases κ1 with
      | init => exact htr.elim
      | appendFree z =>
        obtain ⟨rfl, -⟩ := htr
        have hz : z < C.ip.m := (hpt1.2.1 (z, 1) (by simp)).1
        refine binSearch_spec hX hpre hpt0.1 hpt0.2.1 (by have := hpt0.2.2; omega) hz (.inr ?_)
        rwa [MergeH.sandwich_comm] at hsand
      | removeComplete Xs h Y Z =>
        obtain ⟨rfl, rfl, hh, hZ, hf⟩ := htr
        have e : Xs ++ (some h).toList ++ Y = Xs ++ h :: Y := by simp
        refine stepC_spec hX hpre (h := some h) (by rw [e]; exact hpt0.1) hpt1.1 ?_ hZ
          (by simpa using hh) hf (by rw [e]; exact hsand) dflt
        intro a ha
        rw [e] at ha
        rcases List.mem_append.1 ha with ha | ha
        · exact hpt0.2.1 a ha
        · exact hpt1.2.1 a (List.mem_append_right _ ha)
      | toRegular =>
        exfalso
        obtain ⟨A, B, z, rfl, rfl⟩ := htr
        rw [MergeH.cnt_toRegular, MergeH.sandwich_iff] at hsand
        omega
    next hff =>
      have h1 := MergeH.firstFlip_none' hff (fun x hx ↦ by
        obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hx
        exact hne w hw') (pts.length - 1) (by rw [List.length_map]; omega)
      have hhead : pts[0] = (H'p, .init) := by
        have := hinv.head
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at this
        exact Option.some.inj this
      have hlast' : pts[pts.length - 1] = (cur, κ) := by
        have := hlast
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      rw [MergeH.getD_of_lt (by rw [List.length_map]; omega), List.getElem_map, hlast',
        MergeH.getD_of_lt (by rw [List.length_map]; omega), List.getElem_map, hhead,
        decide_eq_decide] at h1
      have hc1 := hne _ (List.mem_of_getLast? hlast)
      have hc0 := hne (H'p, .init) (by rw [← hhead]; exact List.getElem_mem hlen)
      dsimp only at h1 hc0 hc1
      rw [hlast]
      dsimp only [Option.getD_some]
      have hcur : Hp ++ [] ++ cur.drop Hp.length = cur := by
        rw [List.append_nil]
        exact List.prefix_iff_eq_append.1 hpref
      have hptc := hinv.pt _ (List.mem_of_getLast? hlast)
      have hnew := MergeH.Hp_new hHp
      refine stepC_spec hX hpre (Xs := Hp) (h := none) (Y := []) (Z := cur.drop Hp.length)
        (by rw [Option.toList, List.append_nil, List.append_nil]; exact MergeH.Hp_vs hX hpre.ok hHp)
        (by rw [hcur]; exact hptc.1) ?_
        (fun a ha ↦ hcreg a (List.mem_of_mem_drop ha)) (by simp) ?_ ?_ dflt
      · intro a ha
        simp only [Option.toList, List.append_nil, List.mem_append] at ha
        rcases ha with ha | ha
        · exact MergeH.Hp_ok hHp a ha
        · exact hptc.2.1 a (List.mem_of_mem_drop ha)
      · rw [List.append_nil, MergeH.nFreeSeqA_eq_zero fun a ha ↦ (hnew a ha).1]
        omega
      · rw [hcur]
        simp only [Option.toList, List.append_nil]
        rw [MergeH.sandwich_iff] at hs ⊢
        by_cases h2 : C.cnt (C.fhat b) pre H'p < C.ip.k
        · have := h1.2 h2
          omega
        · have : ¬ C.cnt (C.fhat b) pre cur < C.ip.k := fun h3 ↦ h2 (h1.1 h3)
          omega

/-- **Step A** ([BCFGJPSSV26a, Claim D.12] with [BCFGJPSSV26a, Lemma D.9]): under the promise,
sequence `p` of `H'` is `η`-valid after the first `p` sequences of `H`, at the opening cost of
`H`, so their completion is a solution. -/
theorem stepA_spec {p : ℕ} (hp : p < 2 * C.ip.R) {pr : Pair} (h : Promise hX p pr) :
    PreOK hX p pr.b (pr.H.take p) ∧
    ValidSeq C.par X.d (C.fhat pr.b) C.ip.η p (decS hX (pr.H.take p).flatten)
      (decS hX (pr.H'.getD p [])) ∧
    (∀ a ∈ pr.H'.getD p [], C.AtomOK a ∧ a.2 = 0) ∧
    pr.H.getD p [] = C.completeSeq (typ1 p) (C.fhat pr.b) (C.θseq p) (pr.H.take p).flatten [] ∧
    Sol C.par X.d (C.fhat pr.b) C.ip.η
      (decH hX (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []]))) := by
  obtain ⟨hlenH, hlenH'⟩ := h.length
  have hpre : PreOK hX p pr.b (pr.H.take p) := by
    refine ⟨by simp [hlenH]; omega, hp, h.b_le, ?_, MergeH.SolOK.take h.ok p, fun q ↦ ?_⟩
    · rw [MergeH.decH_take]
      exact MergeH.EtaValid.take h.sol.2.1 p
    · by_cases hq : q < p
      · rw [MergeH.getD_take hq]
        exact (h.free3 q).1
      · rw [MergeH.getD_of_le (by simp; omega)]
        exact Nat.zero_le _
  have hH'p : pr.H'.getD p [] =
      C.completeSeq (typ1 p) (C.fhat pr.b') (C.θseq p) (pr.H'.take p).flatten [] := by
    have := C.complete_getD (C.fhat pr.b') (H := pr.H'.take p) (p := p) (by simp) hp
    rwa [h.det'] at this
  have hHp : pr.H.getD p [] =
      C.completeSeq (typ1 p) (C.fhat pr.b) (C.θseq p) (pr.H.take p).flatten [] := by
    have := C.complete_getD (C.fhat pr.b) (H := pr.H.take p) (p := p) (by simp) hp
    rwa [h.det] at this
  have hokH' := MergeH.SolOK.take h.ok' p
  have h0 : ValidSeq C.par X.d (C.fhat pr.b') 0 p (decS hX (pr.H'.take p).flatten)
      (decS hX (pr.H'.getD p [])) := by
    rw [hH'p]
    exact completeSeq_validSeq hX (nη_lt_fhat hX _) le_rfl
      (fun a ha ↦ hokH' a (by simpa using ha)) (fun t ht ↦ absurd ht (by simp))
  have hno' := MergeH.noOver_pre hX (b := pr.b') (pre := pr.H'.take p) (p := p)
    (by simp [hlenH']; omega) (by rw [MergeH.decH_take]; exact MergeH.EtaValid.take h.sol'.2.1 p)
    []
  rw [List.append_nil] at hno'
  have hval : ValidSeq C.par X.d (C.fhat pr.b) C.ip.η p (decS hX (pr.H.take p).flatten)
      (decS hX (pr.H'.getD p [])) := by
    rcases h.diff with ⟨hbb, hff, htake⟩ | ⟨hbb, q, hq, t, z, g, -, hat, htake⟩
    · rw [htake]
      exact ValidSeq.param_f hX.good (fun j i ↦ X.d_nonneg j i)
        (by have := hX.two_le_n; omega) (fhat_mono hX hbb.le) hff h0 hno'
    · have hat' : ((pr.H.take p).getD q []).getD t (0, 0) = (z, g + 1) := by
        rw [MergeH.getD_take hq]
        exact hat
      obtain ⟨A, B, hA, hB⟩ := flatten_offset (L := pr.H.take p) (by simp; omega) hat'
        (z, g + 1 + 1)
      rw [show (z, g + 2) = (z, g + 1 + 1) from rfl, ← htake] at hB
      rw [hB, decS_append, MergeH.decS_cons, MergeH.decA_free_mk, ← hbb] at h0 hno'
      rw [hA, decS_append, MergeH.decS_cons, MergeH.decA_free_mk]
      exact ValidSeq.param_u hX.good (fun j i ↦ X.d_nonneg j i) (MergeH.off_nonneg hX g)
        (MergeH.off_le_succ hX g) (by have := off_succ_sub_le hX g; linarith) h0 hno'
  have hok'p : ∀ a ∈ pr.H'.getD p [], C.AtomOK a ∧ a.2 = 0 := by
    intro a ha
    refine ⟨MergeH.SolOK.getD h.ok' p a ha, ?_⟩
    rw [hH'p] at ha
    exact (C.completeSeq_new _ _ _ _ [] a (by simpa using ha)).1
  exact ⟨hpre, hval, hok'p, hHp, (MergeH.complete_sol_pre hX hpre.len hp h.b_le hpre.valid
    hpre.ok hval fun a ha ↦ (hok'p a ha).1).1⟩

/-- **Bisection** ends with a good output or gives the promise before phase `0`. -/
theorem bisect_spec :
    (∃ H b, C.bisect = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr, C.bisect = .cont pr ∧ Promise hX 0 pr) := by
  have hsol : ∀ b, b ≤ 2 ^ C.ip.Pf → Sol C.par X.d (C.fhat b) C.ip.η (decH hX (C.sol b)) ∧
      C.SolOK (C.sol b) ∧ ∀ q, nFreeSeqA ((C.sol b).getD q []) = 0 := fun b hb ↦ by
    obtain ⟨h1, h2, h3⟩ := sol_sol hX hb
    exact ⟨MergeH.Sol.mono_η h1 hX.good.η_nonneg, h2, h3⟩
  have hgood : ∀ b, b ≤ 2 ^ C.ip.Pf →
      (nRegA (C.sol b) = C.ip.k ∨ (nRegA (C.sol b) ≤ C.ip.k ∧ b = 0)) →
      GoodOut hX (C.sol b) b := by
    intro b hb hc
    obtain ⟨h1, h2, h3⟩ := hsol b hb
    have h4 : 1 ≤ nRegA (C.sol b) := by
      refine one_le_nRegA_of_sol hX (sol_sol hX hb).1 fun a ha ↦ ?_
      obtain ⟨l, hl, ha⟩ := List.mem_flatten.1 ha
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hl
      have := h3 q
      rw [MergeH.getD_of_lt hq] at this
      exact MergeH.reg_of_nFreeSeqA_eq_zero this a ha
    refine ⟨h1, h2, hb, fun q ↦ by rw [h3 q]; omega, ?_, h4⟩
    rcases hc with hc | ⟨hc, rfl⟩
    · exact .inl hc
    · exact .inr ⟨hc, rfl, h3⟩
  unfold bisect
  by_cases h0 : nRegA (C.sol 0) ≤ C.ip.k
  · rw [if_pos h0]
    exact .inl ⟨_, _, rfl, hgood 0 (Nat.zero_le _) (.inr ⟨h0, rfl⟩)⟩
  rw [if_neg h0]
  by_cases hT : nRegA (C.sol (2 ^ C.ip.Pf)) = C.ip.k
  · rw [if_pos hT]
    exact .inl ⟨_, _, rfl, hgood _ le_rfl (.inl hT)⟩
  rw [if_neg hT]
  have hT1 := nRegA_sol_top_le_one hX
  have hs : sandwich (nRegA (C.sol 0)) (nRegA (C.sol (2 ^ C.ip.Pf))) C.ip.k = true := by
    rw [MergeH.sandwich_iff]
    have := hX.one_le_k
    omega
  rcases searchStep_spec (c := fun b ↦ nRegA (C.sol b)) (P := C.ip.Pf) hs with
    ⟨lo, heq, hlo, hsand, -⟩ | ⟨lo, hi, g, heq, hg, hgle⟩
  · rw [heq]
    obtain ⟨h1, h2, h3⟩ := hsol (lo + 1) hlo
    obtain ⟨h1', h2', h3'⟩ := hsol lo (by omega)
    refine .inr ⟨_, rfl, h1, h1', h2, h2', hlo, Nat.le_of_succ_le hlo, ?_,
      .inl ⟨Nat.lt_succ_self lo, fhat_succ_sub_le hX lo, by rw [List.take_zero, List.take_zero]⟩,
      by dsimp only; rw [List.take_zero, sol], by dsimp only; rw [List.take_zero, sol],
      fun q ↦ ⟨by rw [h3 q]; omega, by rw [h3' q]; omega⟩⟩
    rw [MergeH.sandwich_comm]
    exact hsand
  · rw [heq]
    exact .inl ⟨_, _, rfl, hgood g hgle (.inl hg)⟩

/-- **A phase** ends with a good output or keeps the promise for the next phase. -/
theorem phase_spec {p : ℕ} (hp : p < 2 * C.ip.R) {pr : Pair} (h : Promise hX p pr) :
    (∃ H b, C.phase p pr = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr', C.phase p pr = .cont pr' ∧ Promise hX (p + 1) pr') := by
  obtain ⟨hpre, hval, hok'p, hHp, hsol''⟩ := stepA_spec hX hp h
  obtain ⟨hlenH, hlenH'⟩ := h.length
  have hokW : ∀ a ∈ pr.H'.getD p [], C.AtomOK a := fun a ha ↦ (hok'p a ha).1
  have hok'' :=
    (MergeH.complete_sol_pre hX hpre.len hp h.b_le hpre.valid hpre.ok hval hokW).2
  have hfW : nFreeSeqA (pr.H'.getD p []) = 0 :=
    MergeH.nFreeSeqA_eq_zero fun a ha ↦ (hok'p a ha).2
  have hfree'' := PreOK.free_complete hX hpre (C.fhat pr.b) (W := pr.H'.getD p []) (by omega)
  have htake'' := MergeH.complete_take_succ (C := C) (f := C.fhat pr.b) hpre.len hp
    (pr.H'.getD p [])
  unfold phase
  dsimp only
  by_cases hk : nRegA (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])) = C.ip.k
  · rw [if_pos hk]
    exact .inl ⟨_, _, rfl, hsol'', hok'', h.b_le, hfree'', .inl hk, hk ▸ hX.one_le_k⟩
  rw [if_neg hk]
  by_cases hs : sandwich (nRegA (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])))
    (nRegA pr.H') C.ip.k = true
  · rw [if_pos hs]
    refine .inr ⟨_, rfl, hsol'', h.sol', hok'', h.ok', h.b_le, h.b'_le, hs, ?_, ?_, ?_,
      fun q ↦ ⟨hfree'' q, (h.free3 q).2⟩⟩
    · rcases h.diff with ⟨hbb, hff, htake⟩ | ⟨hbb, q, hq, t, z, g, hg, hat, htake⟩
      · refine .inl ⟨hbb, hff, ?_⟩
        dsimp only
        rw [htake'', MergeH.take_succ_getD (d := []) (show p < pr.H'.length by omega), htake]
      · refine .inr ⟨hbb, q, by omega, t, z, g, hg, ?_, ?_⟩
        · dsimp only
          rw [MergeH.complete_getD_lt hpre.len hp _ hq, MergeH.getD_take hq]
          exact hat
        · dsimp only
          rw [htake'', MergeH.take_succ_getD (d := []) (show p < pr.H'.length by omega), htake,
            MergeH.modify_append_left (by simp; omega)]
    · dsimp only
      rw [htake'']
    · dsimp only
      rw [MergeH.take_succ_getD (d := []) (show p < pr.H'.length by omega), h.getD_H' hX hp]
      have := C.complete_succ (C.fhat pr.b') (H := pr.H'.take p) (by simp; omega)
      rw [show (pr.H'.take p).length = p by simp; omega] at this
      rw [this, h.det']
  rw [if_neg hs]
  rw [MergeH.complete_getD_self hpre.len hp]
  have hwalk := walkPhase_spec hX hpre hHp hval hokW (fun a ha ↦ (hok'p a ha).2) ?_
    (.done pr.H pr.b)
  · rcases hwalk with ⟨H, h1, h2⟩ | ⟨pr', h1, h2⟩
    · exact .inl ⟨H, pr.b, h1, h2⟩
    · exact .inr ⟨pr', h1, h2⟩
  have hcH : C.cnt (C.fhat pr.b) (pr.H.take p) (pr.H.getD p []) = nRegA pr.H := by
    change nRegA (C.complete _ (pr.H.take p ++ [pr.H.getD p []])) = _
    have := C.complete_succ (C.fhat pr.b) (H := pr.H.take p) (by rw [hpre.len]; exact hp)
    rw [hpre.len] at this
    rw [hHp, this, h.det]
  have hcW : C.cnt (C.fhat pr.b) (pr.H.take p) (pr.H'.getD p []) =
      nRegA (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])) := rfl
  rw [hcH, hcW]
  have h1 := h.sand
  rw [MergeH.sandwich_iff] at h1 hs ⊢
  omega

/-- The merge after `q ≤ 2R` phases ends with a good output or keeps the promise. -/
theorem mergeUpTo_spec {q : ℕ} (hq : q ≤ 2 * C.ip.R) :
    (∃ H b, C.mergeUpTo q = .done H b ∧ GoodOut hX H b) ∨
      (∃ pr, C.mergeUpTo q = .cont pr ∧ Promise hX q pr) := by
  induction q with
  | zero => exact bisect_spec hX
  | succ q ih =>
    have hmerge : C.mergeUpTo (q + 1) = C.mergeStep (C.mergeUpTo q) q := by
      simp [mergeUpTo, List.range_succ, List.foldl_append]
    rcases ih (by omega) with ⟨H, b, hd, hg⟩ | ⟨pr, hc, hpr⟩
    · exact .inl ⟨H, b, by rw [hmerge, hd]; rfl, hg⟩
    · rw [hmerge, hc]
      exact phase_spec hX (by omega) hpr

/-- **The merge ends with a good output.** -/
theorem merge_spec : GoodOut hX C.merge.1 C.merge.2 := by
  rcases mergeUpTo_spec hX (le_refl (2 * C.ip.R)) with ⟨H, b, hd, hg⟩ | ⟨pr, -, hpr⟩
  · simp only [merge, hd]
    exact hg
  · exact absurd hpr (not_promise_end hX)

end Ctx

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.merge_spec := @BCFGJPSSV26.Greedy.Ctx.merge_spec
