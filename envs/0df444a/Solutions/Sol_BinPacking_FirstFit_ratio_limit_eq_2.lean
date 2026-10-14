-- Prove2me | solution 2 for BinPacking.FirstFit.ratio_limit_eq
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T08:43:25.719841+00:00
-- url     : https://prove2.me/submissions/272e7f2b-28d7-4fcb-8792-2a44fdb08726

-- Complete checked reconstruction of the native First-Fit and Best-Fit asymptotic ratio theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W
import Mathlib


-- Begin Canonical

namespace BinPacking.FirstFit.Proof
end BinPacking.FirstFit.Proof
-- End Canonical

-- Begin RunBasics

namespace BinPacking.FirstFit.Proof

@[simp] theorem run_nil (choose : List (List ℝ) → ℝ → ℕ) : run choose [] = [] := rfl

theorem run_append (choose : List (List ℝ) → ℝ → ℕ) (L K : List ℝ) :
    run choose (L ++ K) = K.foldl (fun bins a => placeAt bins (choose bins a) a) (run choose L) := by
  simp [run,List.foldl_append]

@[simp] theorem run_snoc (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (a : ℝ) :
    run choose (L ++ [a]) = placeAt (run choose L) (choose (run choose L) a) a := by
  simp [run_append]

theorem placeAt_length (B : List (List ℝ)) (j : ℕ) (a : ℝ) :
    (placeAt B j a).length = if j < B.length then B.length else B.length+1 := by
  unfold placeAt
  split_ifs <;> simp

theorem placeAt_length_le (B : List (List ℝ)) (j : ℕ) (a : ℝ) :
    B.length ≤ (placeAt B j a).length := by rw [placeAt_length]; split_ifs <;> omega

theorem placeAt_length_le_succ (B : List (List ℝ)) (j : ℕ) (a : ℝ) :
    (placeAt B j a).length ≤ B.length+1 := by rw [placeAt_length]; split_ifs <;> omega

theorem placeAt_getElem (B : List (List ℝ)) (j : ℕ) (a : ℝ) (i : ℕ) (hi : i < B.length) :
    (placeAt B j a)[i]'(lt_of_lt_of_le hi (placeAt_length_le B j a)) =
      if i=j then B[i]++[a] else B[i] := by
  unfold placeAt
  split_ifs with hj
  · simp
  · have hij : i ≠ j := by omega
    simp [List.getElem_append_left,hi,hij]

theorem placeAt_getD (B : List (List ℝ)) (j : ℕ) (a : ℝ) (i : ℕ) (hi : i < B.length) :
    (placeAt B j a).getD i [] = if i=j then B.getD i []++[a] else B.getD i [] := by
  rw [List.getD_eq_getElem _ _ (lt_of_lt_of_le hi (placeAt_length_le B j a)),
    List.getD_eq_getElem _ _ hi,placeAt_getElem]

theorem placeAt_new (B : List (List ℝ)) (j : ℕ) (a : ℝ) (hj : B.length ≤ j) :
    (placeAt B j a).getD B.length [] = [a] := by
  rw [placeAt,if_neg (not_lt.mpr hj),List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem placeAt_getD_all (B : List (List ℝ)) (j : ℕ) (a : ℝ) (hj : j ≤ B.length) (i : ℕ) :
    (placeAt B j a).getD i [] = if i=j then B.getD i []++[a] else B.getD i [] := by
  by_cases hi : i < B.length
  · exact placeAt_getD B j a i hi
  · by_cases hij : i=j
    · subst i
      have he : j=B.length := by omega
      subst j
      rw [placeAt_new B B.length a le_rfl,List.getD_eq_default _ _ le_rfl]
      simp
    · have hlen : (placeAt B j a).length ≤ i := by
        rw [placeAt_length]
        split_ifs <;> omega
      rw [List.getD_eq_default _ _ hlen,List.getD_eq_default _ _ (by omega),if_neg hij]

theorem placeAt_measure (B : List (List ℝ)) (j : ℕ) (a : ℝ) (hj : j ≤ B.length)
    (f : ℝ → ℝ) (i : ℕ) :
    (((placeAt B j a).getD i []).map f).sum = ((B.getD i []).map f).sum + if i=j then f a else 0 := by
  rw [placeAt_getD_all B j a hj i]
  split_ifs <;> simp

end BinPacking.FirstFit.Proof
-- End RunBasics

-- Begin ChoiceRules

namespace BinPacking.FirstFit.Proof

def ChoiceRule (choose : List (List ℝ) → ℝ → ℕ) : Prop :=
  ∀ B a, choose B a ≤ B.length ∧
    (choose B a < B.length → (B.getD (choose B a) []).sum+a≤1) ∧
    (choose B a = B.length → ∀ C ∈ B, 1<C.sum+a)

theorem ff_choice_rule : ChoiceRule ffChoice := by
  classical
  intro B a
  refine ⟨List.findIdx_le_length,?_,?_⟩
  · intro h
    have hh := @List.findIdx_getElem (List ℝ) (fun C => decide (C.sum+a≤1)) B h
    rw [List.getD_eq_getElem _ _ h]
    exact of_decide_eq_true hh
  · intro h C hC
    have hh := (List.findIdx_eq_length.mp h) C hC
    simpa using hh

theorem bf_fitting_exists (B : List (List ℝ)) (a : ℝ) (h : ∃ C ∈ B, C.sum+a≤1) :
    ∃ C ∈ B, C.sum+a≤1 ∧ ∀ D ∈ B, D.sum+a≤1 → D.sum≤C.sum := by
  classical
  let S := B.toFinset.filter (fun C => C.sum+a≤1)
  have hs : S.Nonempty := by
    obtain ⟨C,hC,hfit⟩ := h
    exact ⟨C,by simp [S,hC,hfit]⟩
  obtain ⟨C,hC,hm⟩ := S.exists_max_image (fun C => C.sum) hs
  have hc := Finset.mem_filter.mp hC
  refine ⟨C,by simpa using hc.1,hc.2,?_⟩
  intro D hD hfit
  exact hm D (by simp [S,hD,hfit])

theorem bf_choice_rule : ChoiceRule bfChoice := by
  classical
  intro B a
  refine ⟨List.findIdx_le_length,?_,?_⟩
  · intro h
    have hh := @List.findIdx_getElem (List ℝ)
      (fun C => decide (C.sum+a≤1 ∧ ∀ D ∈ B, D.sum+a≤1 → D.sum≤C.sum)) B h
    have hp : B[bfChoice B a].sum+a≤1 ∧ ∀ D ∈ B,D.sum+a≤1→D.sum≤B[bfChoice B a].sum := by
      exact of_decide_eq_true hh
    simpa only [List.getD_eq_getElem _ _ h] using hp.1
  · intro he C hC
    by_contra hh
    obtain ⟨D,hD,hd⟩ := bf_fitting_exists B a ⟨C,hC,le_of_not_gt hh⟩
    have ht : bfChoice B a < B.length := List.findIdx_lt_length_of_exists ⟨D,hD,by simpa using hd⟩
    omega

theorem ff_before (B : List (List ℝ)) (a : ℝ) (j : ℕ) (hj : j < ffChoice B a) :
    1 < (B.getD j []).sum+a := by
  have hlen : j < B.length := lt_of_lt_of_le hj List.findIdx_le_length
  have hh := List.not_of_lt_findIdx hj
  simpa only [List.getD_eq_getElem _ _ hlen,decide_eq_false_iff_not,not_le] using hh

theorem bf_dominates (B : List (List ℝ)) (a : ℝ) (j : ℕ) (hj : j < B.length)
    (hfit : (B.getD j []).sum+a≤1) :
    bfChoice B a < B.length ∧ (B.getD j []).sum ≤ (B.getD (bfChoice B a) []).sum := by
  have hex := bf_fitting_exists B a ⟨B[j],List.getElem_mem hj,by simpa only [List.getD_eq_getElem _ _ hj] using hfit⟩
  obtain ⟨C,hC,hmax⟩ := hex
  have hb : bfChoice B a < B.length := List.findIdx_lt_length_of_exists ⟨C,hC,by simpa using hmax⟩
  have hh := @List.findIdx_getElem (List ℝ)
    (fun C => decide (C.sum+a≤1 ∧ ∀ D ∈ B,D.sum+a≤1→D.sum≤C.sum)) B hb
  simp only [decide_eq_true_eq] at hh
  refine ⟨hb,?_⟩
  rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hb]
  exact hh.2 B[j] (List.getElem_mem hj) (by simpa only [List.getD_eq_getElem _ _ hj] using hfit)

end BinPacking.FirstFit.Proof
-- End ChoiceRules

-- Begin RunHistory

namespace BinPacking.FirstFit.Proof

noncomputable def historyMeasure (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ)
    (f : ℝ → ℝ) (k j : ℕ) : ℝ :=
  ∑ i : Fin L.length, if i.val<k ∧ binOf choose L i=j then f (L.get i) else 0

theorem historyMeasure_succ (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ)
    (f : ℝ → ℝ) (k j : ℕ) (hk : k<L.length) :
    historyMeasure choose L f (k+1) j = historyMeasure choose L f k j +
      if binOf choose L ⟨k,hk⟩=j then f L[k] else 0 := by
  classical
  have he : ∀ i : Fin L.length,
      (if i.val<k+1 ∧ binOf choose L i=j then f (L.get i) else 0) =
      (if i.val<k ∧ binOf choose L i=j then f (L.get i) else 0)+
      (if i=⟨k,hk⟩ then (if binOf choose L i=j then f (L.get i) else 0) else 0) := by
    intro i
    by_cases hi : i=⟨k,hk⟩
    · subst i; simp
    · have hne : i.val≠k := fun h => hi (Fin.ext h)
      have hh : i.val<k+1 ↔ i.val<k := by omega
      simp [hi,hh]
  simp only [historyMeasure,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_pos]
  rfl

theorem run_measure_take (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (L : List ℝ) (f : ℝ → ℝ) (k : ℕ) (hk : k≤L.length) (j : ℕ) :
    (((run choose (L.take k)).getD j []).map f).sum = historyMeasure choose L f k j := by
  induction k with
  | zero => simp [historyMeasure]
  | succ k ih =>
    have hkn : k<L.length := by omega
    rw [List.take_succ_eq_append_getElem hkn,run_snoc,
      placeAt_measure _ _ _ (hr _ _).1,ih (by omega),historyMeasure_succ choose L f k j hkn]
    simp only [binOf,eq_comm,List.get_eq_getElem]

theorem run_measure (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (L : List ℝ) (f : ℝ → ℝ) (j : ℕ) :
    (((run choose L).getD j []).map f).sum =
      ∑ i ∈ Finset.univ.filter (fun i : Fin L.length => binOf choose L i=j), f (L.get i) := by
  have hh := run_measure_take choose hr L f L.length le_rfl j
  simpa [historyMeasure,Finset.sum_filter] using hh

end BinPacking.FirstFit.Proof
-- End RunHistory

-- Begin RunLoads

namespace BinPacking.FirstFit.Proof

def GoodBins (B : List (List ℝ)) : Prop := ∀ C ∈ B, C≠[] ∧ IsList C ∧ C.sum≤1

theorem isList_append {L K : List ℝ} (hL : IsList L) (hK : IsList K) : IsList (L++K) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hL a ha
  · exact hK a ha

theorem placeAt_good (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (B : List (List ℝ)) (a : ℝ) (hB : GoodBins B) (ha : 0<a ∧ a≤1) :
    GoodBins (placeAt B (choose B a) a) := by
  intro C hC
  by_cases hj : choose B a<B.length
  · simp only [placeAt,if_pos hj,List.mem_mapIdx] at hC
    obtain ⟨i,hi,hC⟩ := hC
    by_cases he : i=choose B a
    · subst i
      subst C
      simp only [ite_true]
      have hb := hB _ (List.getElem_mem hj)
      refine ⟨by simp,isList_append (L := B[choose B a]) (K := [a]) hb.2.1 (by simpa [IsList] using ha),?_⟩
      have hf := (hr B a).2.1 hj
      rw [List.getD_eq_getElem _ _ hj] at hf
      simpa using hf
    · simp only [if_neg he] at hC
      subst C
      exact hB _ (List.getElem_mem hi)
  · simp only [placeAt,if_neg hj,List.mem_append,List.mem_singleton] at hC
    rcases hC with hC | rfl
    · exact hB _ hC
    · exact ⟨by simp,by simpa [IsList] using ha,by simpa using ha.2⟩

theorem run_good (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (L : List ℝ) (hL : IsList L) : GoodBins (run choose L) := by
  have aux : ∀ (K : List ℝ) (B : List (List ℝ)), IsList K → GoodBins B →
      GoodBins (K.foldl (fun bins a => placeAt bins (choose bins a) a) B) := by
    intro K
    induction K with
    | nil => intro B _ hB; exact hB
    | cons a K ih =>
      intro B hK hB
      apply ih _ (fun x hx => hK x (by simp [hx]))
      exact placeAt_good choose hr B a hB (hK a (by simp))
  exact aux L [] hL (by intro C hC; simp at hC)

theorem fold_length_mono (choose : List (List ℝ) → ℝ → ℕ) (K : List ℝ) (B : List (List ℝ)) :
    B.length ≤ (K.foldl (fun bins a => placeAt bins (choose bins a) a) B).length := by
  induction K generalizing B with
  | nil => exact le_rfl
  | cons a K ih => exact (placeAt_length_le B (choose B a) a).trans (ih _)

theorem run_take_length_le (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (k : ℕ) :
    (run choose (L.take k)).length ≤ (run choose L).length := by
  have hh := fold_length_mono choose (L.drop k) (run choose (L.take k))
  rw [← run_append,List.take_append_drop] at hh
  exact hh

theorem binOf_lt_run_length (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (L : List ℝ) (i : Fin L.length) : binOf choose L i < (run choose L).length := by
  have hle := (hr (run choose (L.take i.val)) (L.get i)).1
  have hlt : binOf choose L i < (run choose (L.take (i.val+1))).length := by
    rw [List.take_succ_eq_append_getElem i.isLt,run_snoc,placeAt_length]
    change choose _ _ < _
    split_ifs <;> omega
  exact hlt.trans_le (run_take_length_le choose L (i.val+1))

theorem run_load (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (L : List ℝ) (j : ℕ) : ((run choose L).getD j []).sum =
      ∑ i ∈ Finset.univ.filter (fun i : Fin L.length => binOf choose L i=j), L.get i := by
  simpa using run_measure choose hr L id j

end BinPacking.FirstFit.Proof
-- End RunLoads

-- Begin RunSeparation

namespace BinPacking.FirstFit.Proof

def Separated (B : List (List ℝ)) : Prop :=
  ∀ i j, i < B.length → j < B.length → i ≠ j →
    1 < (B.getD i []).sum + (B.getD j []).sum

theorem placeAt_load_mono (B : List (List ℝ)) (k : ℕ) (a : ℝ) (hk : k ≤ B.length)
    (ha : 0 ≤ a) (i : ℕ) :
    (B.getD i []).sum ≤ ((placeAt B k a).getD i []).sum := by
  rw [placeAt_getD_all B k a hk i]
  split_ifs
  · simp only [List.sum_append,List.sum_singleton]; linarith
  · exact le_rfl

theorem placeAt_separated (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (B : List (List ℝ)) (a : ℝ) (ha : 0 ≤ a) (hB : Separated B) :
    Separated (placeAt B (choose B a) a) := by
  intro i j hi hj hij
  have hk := (hr B a).1
  have hm := placeAt_load_mono B (choose B a) a hk ha
  by_cases hi' : i < B.length
  · by_cases hj' : j < B.length
    · have hh := hB i j hi' hj' hij
      linarith [hm i,hm j]
    · have hk' : choose B a = B.length := by
        rw [placeAt_length] at hj
        split_ifs at hj <;> omega
      have hj'': j = B.length := by
        rw [placeAt_length] at hj
        split_ifs at hj <;> omega
      subst j
      have hh := (hr B a).2.2 hk' _ (List.getElem_mem hi')
      rw [← List.getD_eq_getElem _ _ hi'] at hh
      rw [placeAt_new B _ a hk'.ge]
      simp only [List.sum_singleton]
      linarith [hm i]
  · have hi'': i = B.length := by
      rw [placeAt_length] at hi
      split_ifs at hi <;> omega
    have hj' : j < B.length := by
      rw [placeAt_length] at hj
      split_ifs at hj <;> omega
    have hk' : choose B a = B.length := by
      rw [placeAt_length] at hi
      split_ifs at hi <;> omega
    subst i
    have hh := (hr B a).2.2 hk' _ (List.getElem_mem hj')
    rw [← List.getD_eq_getElem _ _ hj'] at hh
    rw [placeAt_new B _ a hk'.ge]
    simp only [List.sum_singleton]
    linarith [hm j]

def EarlyRule (choose : List (List ℝ) → ℝ → ℕ) : Prop :=
  ∀ B a, Separated B → (B.getD (choose B a) []).sum ≤ 1/2 →
    ∀ j, j < choose B a → 1 < (B.getD j []).sum+a

theorem ff_early_rule : EarlyRule ffChoice := by
  intro B a _ _ j hj
  exact ff_before B a j hj

theorem bf_early_rule : EarlyRule bfChoice := by
  intro B a hB hs j hj
  have hr := bf_choice_rule B a
  by_cases he : bfChoice B a = B.length
  · exact hr.2.2 he _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _)
  · have hb : bfChoice B a < B.length := by omega
    by_contra hh
    have hd := (bf_dominates B a j (by omega) (le_of_not_gt hh)).2
    have hp := hB j (bfChoice B a) (by omega) hb (by omega)
    linarith

end BinPacking.FirstFit.Proof
-- End RunSeparation

-- Begin RunEarly

namespace BinPacking.FirstFit.Proof

def Early (r : ℝ) (C : List ℝ) : Prop :=
  ∀ a R, C=a::R → r<a ∧ (a≤1/2 → ∀ b S, R=b::S → r<b)

theorem Early.mono {r t : ℝ} {C : List ℝ} (h : Early r C) (ht : t≤r) : Early t C := by
  intro a R he
  have hh := h a R he
  exact ⟨ht.trans_lt hh.1,fun ha b S hS => ht.trans_lt (hh.2 ha b S hS)⟩

theorem early_singleton {r a : ℝ} (h : r<a) : Early r [a] := by
  intro b S he
  simp only [List.cons.injEq] at he
  obtain ⟨rfl,rfl⟩ := he
  exact ⟨h,by intro _ c T hT; simp at hT⟩

theorem early_append {r a : ℝ} {C : List ℝ} (h : Early r C)
    (ha : C.sum≤1/2 → r<a) : Early r (C++[a]) := by
  cases C with
  | nil => exact early_singleton (ha (by norm_num))
  | cons b R =>
    have hh := h b R rfl
    intro c S he
    simp only [List.cons_append,List.cons.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    refine ⟨hh.1,?_⟩
    intro hb d T hd
    cases R with
    | nil =>
      simp only [List.nil_append,List.cons.injEq] at hd
      obtain ⟨rfl,rfl⟩ := hd
      exact ha (by simpa using hb)
    | cons e R =>
      simp only [List.cons_append,List.cons.injEq] at hd
      obtain ⟨rfl,_⟩ := hd
      exact hh.2 hb e R rfl

def EarlyBins (B : List (List ℝ)) : Prop :=
  ∀ i, i < B.length → ∀ j, j < i → Early (1-(B.getD j []).sum) (B.getD i [])

theorem placeAt_early (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (he : EarlyRule choose) (B : List (List ℝ)) (a : ℝ) (ha : 0≤a)
    (hB : Separated B) (hE : EarlyBins B) : EarlyBins (placeAt B (choose B a) a) := by
  intro i hi j hj
  have hk := (hr B a).1
  have hm := placeAt_load_mono B (choose B a) a hk ha j
  by_cases hi' : i<B.length
  · have hold := (hE i hi' j hj).mono (by linarith :
        1-((placeAt B (choose B a) a).getD j []).sum ≤ 1-(B.getD j []).sum)
    rw [placeAt_getD_all B _ a hk i]
    split_ifs with hik
    · apply early_append hold
      intro hs
      have hh := he B a hB (by simpa only [← hik] using hs) j (by omega)
      linarith
    · exact hold
  · have hi'': i=B.length := by
      rw [placeAt_length] at hi
      split_ifs at hi <;> omega
    have hk' : choose B a=B.length := by
      rw [placeAt_length] at hi
      split_ifs at hi <;> omega
    subst i
    rw [placeAt_new B _ a hk'.ge]
    apply early_singleton
    have hh := (hr B a).2.2 hk' _ (List.getElem_mem hj)
    rw [← List.getD_eq_getElem _ _ hj] at hh
    linarith

theorem run_separated_early (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (he : EarlyRule choose) (L : List ℝ) (hL : IsList L) :
    Separated (run choose L) ∧ EarlyBins (run choose L) := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨by intro i j hi; simp at hi,by intro i hi; simp at hi⟩
  | append_singleton L a ih =>
    have hL' : IsList L := fun x hx => hL x (by simp [hx])
    have ha := (hL a (by simp)).1.le
    obtain ⟨hS,hE⟩ := ih hL'
    rw [run_snoc]
    exact ⟨placeAt_separated choose hr (run choose L) a ha hS,
      placeAt_early choose hr he (run choose L) a ha hS hE⟩

end BinPacking.FirstFit.Proof
-- End RunEarly

-- Begin WeightBasic

namespace BinPacking.FirstFit.Proof

noncomputable def weight (B : List ℝ) : ℝ := (B.map W).sum
noncomputable def bonus (x : ℝ) : ℝ := W x - 6/5*x

theorem W_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ W x := by
  unfold W
  split_ifs <;> linarith

theorem W_small_bounds {x : ℝ} (hx : 0 ≤ x) (h : x ≤ 1/2) :
    6/5*x ≤ W x ∧ W x ≤ 3/2*x ∧ 0 ≤ bonus x ∧ bonus x ≤ 1/10 := by
  unfold bonus W
  split_ifs <;> (refine ⟨?_,?_,?_,?_⟩ <;> linarith)

theorem bonus_zero {x : ℝ} (h : x ≤ 1/6) : bonus x = 0 := by
  simp only [bonus,W,if_pos h,sub_self]

theorem bonus_linear_le {x : ℝ} (h : 1/6 < x) (h' : x ≤ 1/2) :
    bonus x ≤ 3/5*x-1/10 := by
  unfold bonus W
  split_ifs <;> linarith

theorem bonus_lower {x a : ℝ} (_ha : 1/6 ≤ a) (ha' : a ≤ 1/3)
    (hx : a ≤ x) (hx' : x ≤ 1/2) : 3/5*(a-1/6) ≤ bonus x := by
  unfold bonus W
  split_ifs <;> linarith

theorem W_large {x : ℝ} (h : 1/2 < x) : W x = 1 := by
  simp only [W,if_neg (show ¬ x ≤ 1/6 by linarith),if_neg (show ¬ x ≤ 1/3 by linarith),if_neg (not_le.mpr h)]

theorem W_third {x : ℝ} (h : 1/3 < x) : 1/2 < W x := by
  unfold W
  split_ifs <;> linarith

theorem weight_nonneg {B : List ℝ} (h : ∀ x∈B, 0 ≤ x) : 0 ≤ weight B := by
  apply List.sum_nonneg
  intro y hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  exact W_nonneg (h x hx)

theorem weight_small_of_lt {B : List ℝ} (h : IsList B) (hw : weight B < 1) :
    ∀ x∈B, x ≤ 1/2 := by
  intro x hx
  by_contra hh
  have hs : W x ≤ weight B := List.single_le_sum (fun y hy => by
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
    exact W_nonneg (h z hz).1.le) (W x) (List.mem_map.mpr ⟨x,hx,rfl⟩)
  rw [W_large (lt_of_not_ge hh)] at hs
  linarith

end BinPacking.FirstFit.Proof
-- End WeightBasic

-- Begin DeficitScalar

namespace BinPacking.FirstFit.Proof

theorem weight_base_bound {B : List ℝ} (h : ∀ x∈B,0≤x ∧ x≤1/2) :
    6/5*B.sum ≤ weight B := by
  induction B with
  | nil => simp [weight]
  | cons a B ih =>
    have ha := h a (by simp)
    have hh := ih (fun x hx => h x (by simp [hx]))
    have hb := (W_small_bounds ha.1 ha.2).1
    simp only [weight,List.map_cons,List.sum_cons] at *
    linarith

theorem deficit_load {a b α : ℝ} {R : List ℝ}
    (h : IsList (a::b::R)) (hw : weight (a::b::R)<1)
    (ha : α≤a) (hb : α≤b) :
    (a::b::R).sum ≤ 1-α-5/6*(1-weight (a::b::R)) := by
  have hs := weight_small_of_lt h hw
  have hR : ∀ x∈R,0≤x ∧ x≤1/2 := fun x hx =>
    ⟨(h x (by simp [hx])).1.le,hs x (by simp [hx])⟩
  have hbase := weight_base_bound (B := a::b::R) (fun x hx => ⟨(h x hx).1.le,hs x hx⟩)
  by_cases hα : α ≤ 1/6
  · linarith
  · have hα' : 1/6 ≤ α := le_of_lt (lt_of_not_ge hα)
    by_cases ht : α ≤ 1/3
    · have hba := bonus_lower hα' ht ha (hs a (by simp))
      have hbb := bonus_lower hα' ht hb (hs b (by simp))
      have hr := weight_base_bound hR
      simp only [bonus] at hba hbb
      simp only [weight,List.map_cons,List.sum_cons] at hw ⊢ hr
      linarith
    · have hwa := W_third (lt_of_not_ge ht |>.trans_le ha)
      have hwb := W_third (lt_of_not_ge ht |>.trans_le hb)
      have hr := weight_nonneg (B := R) (fun x hx => (hR x hx).1)
      simp only [weight,List.map_cons,List.sum_cons] at hw hr
      linarith

end BinPacking.FirstFit.Proof
-- End DeficitScalar

-- Begin PrefixMaximum

namespace BinPacking.FirstFit.Proof

noncomputable def prefixMax (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => max (prefixMax f k) (f k)

theorem prefixMax_nonneg (f : ℕ → ℝ) (k : ℕ) : 0 ≤ prefixMax f k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (le_max_left _ _)

theorem prefixMax_step (f : ℕ → ℝ) (k : ℕ) : prefixMax f k ≤ prefixMax f (k+1) :=
  le_max_left _ _

theorem prefixMax_le {f : ℕ → ℝ} {k : ℕ} {b : ℝ} (hb : 0≤b)
    (h : ∀ j, j<k → f j≤b) : prefixMax f k≤b := by
  induction k with
  | zero => exact hb
  | succ k ih => exact max_le (ih (fun j hj => h j (by omega))) (h k (by omega))

theorem prefixMax_lt {f : ℕ → ℝ} {k : ℕ} {b : ℝ} (hb : 0<b)
    (h : ∀ j, j<k → f j<b) : prefixMax f k<b := by
  induction k with
  | zero => exact hb
  | succ k ih => exact max_lt (ih (fun j hj => h j (by omega))) (h k (by omega))

theorem sum_increments (a : ℕ → ℝ) (n : ℕ) :
    ∑ k∈Finset.range n,(a (k+1)-a k)=a n-a 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

end BinPacking.FirstFit.Proof
-- End PrefixMaximum

-- Begin StaticDeficit

namespace BinPacking.FirstFit.Proof

noncomputable def coarseAt (P : List (List ℝ)) (i : ℕ) : ℝ :=
  prefixMax (fun j => 1-(P.getD j []).sum) i

noncomputable def deficientSingleton (P : List (List ℝ)) (i : ℕ) : Prop :=
  (P.getD i []).length=1 ∧ weight (P.getD i [])<1

noncomputable def singletonPenalty (P : List (List ℝ)) (i : ℕ) : ℝ :=
  @ite ℝ (deficientSingleton P i) (Classical.propDecidable _) 1 0

theorem coarseAt_le_one {P : List (List ℝ)} (hP : GoodBins P) {i : ℕ}
    (hi : i≤P.length) : coarseAt P i≤1 := by
  apply prefixMax_le (by norm_num)
  intro j hj
  have hb := hP _ (List.getElem_mem (show j<P.length by omega))
  have hs := List.sum_nonneg (fun x hx => (hb.2.1 x hx).1.le)
  rw [List.getD_eq_getElem _ _ (by omega)]
  linarith

theorem coarseAt_lt_head {P : List (List ℝ)} (hP : GoodBins P) (hE : EarlyBins P)
    {i : ℕ} (hi : i<P.length) {a : ℝ} {R : List ℝ} (hC : P.getD i []=a::R) :
    coarseAt P i<a := by
  have hb := hP _ (List.getElem_mem hi)
  rw [← List.getD_eq_getElem P [] hi,hC] at hb
  apply prefixMax_lt (hb.2.1 a (by simp)).1
  intro j hj
  exact (hE i hi j hj a R hC).1

theorem singleton_unique {P : List (List ℝ)} (hP : GoodBins P) (hE : EarlyBins P)
    {i j : ℕ} (hi : i<P.length) (hj : j<P.length)
    (hsi : deficientSingleton P i) (hsj : deficientSingleton P j) : i=j := by
  suffices hh : ∀ i j, i<P.length → j<P.length → deficientSingleton P i →
      deficientSingleton P j → i < j → False by
    rcases lt_trichotomy i j with h | h | h
    · exact (hh i j hi hj hsi hsj h).elim
    · exact h
    · exact (hh j i hj hi hsj hsi h).elim
  intro i j hi hj hsi hsj hij
  obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hsi.1
  obtain ⟨b,hb⟩ := List.length_eq_one_iff.mp hsj.1
  have hgi := hP _ (List.getElem_mem hi)
  have hgj := hP _ (List.getElem_mem hj)
  rw [← List.getD_eq_getElem P [] hi,ha] at hgi
  rw [← List.getD_eq_getElem P [] hj,hb] at hgj
  have hai := weight_small_of_lt hgi.2.1 (by simpa only [ha] using hsi.2) a (by simp)
  have hbj := weight_small_of_lt hgj.2.1 (by simpa only [hb] using hsj.2) b (by simp)
  have he := (hE j hj i hij b [] hb).1
  rw [ha] at he
  simp only [List.sum_singleton] at he
  linarith

theorem deficit_step {P : List (List ℝ)} (hP : GoodBins P) (hE : EarlyBins P)
    {i : ℕ} (hi : i<P.length) :
    max (1-weight (P.getD i [])) 0 ≤
      6/5*(coarseAt P (i+1)-coarseAt P i)+singletonPenalty P i := by
  classical
  unfold singletonPenalty
  have hm : coarseAt P i≤coarseAt P (i+1) := prefixMax_step _ _
  by_cases hw : weight (P.getD i [])<1
  · rw [max_eq_left (by linarith)]
    have hb := hP _ (List.getElem_mem hi)
    rw [← List.getD_eq_getElem P [] hi] at hb
    have hn := weight_nonneg (fun x hx => (hb.2.1 x hx).1.le)
    by_cases hs : deficientSingleton P i
    · rw [if_pos hs]; linarith
    · rw [if_neg hs]
      cases hc : P.getD i [] with
      | nil => exact (hb.1 hc).elim
      | cons a R =>
        cases R with
        | nil => exact (hs ⟨by rw [hc]; rfl,hw⟩).elim
        | cons b R =>
          have hh := hE i hi
          have ha := coarseAt_lt_head hP hE hi hc
          have hsmall := weight_small_of_lt hb.2.1 hw
          have hsa : a≤1/2 := hsmall a (by rw [hc]; simp)
          have hbb : coarseAt P i<b := by
            apply prefixMax_lt (hb.2.1 b (by rw [hc]; simp)).1
            intro j hj
            exact (hh j hj a (b::R) hc).2 hsa b R rfl
          have hd := deficit_load (by simpa only [hc] using hb.2.1)
            (by simpa only [hc] using hw) ha.le hbb.le
          have hm' : 1-(P.getD i []).sum ≤ coarseAt P (i+1) := le_max_right _ _
          rw [hc] at hm'
          linarith
  · rw [max_eq_right (by linarith)]
    have hs : ¬ deficientSingleton P i := fun h => hw h.2
    rw [if_neg hs]
    linarith

end BinPacking.FirstFit.Proof
-- End StaticDeficit

-- Begin StaticUpper

namespace BinPacking.FirstFit.Proof

theorem singleton_penalty_sum {P : List (List ℝ)} (hP : GoodBins P) (hE : EarlyBins P) :
    (∑ i∈Finset.range P.length,singletonPenalty P i) ≤ 1 := by
  classical
  let S := (Finset.range P.length).filter (deficientSingleton P)
  have hc : S.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    exact singleton_unique hP hE (Finset.mem_range.mp hi'.1) (Finset.mem_range.mp hj'.1) hi'.2 hj'.2)
  have hc' : (S.card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa [S,singletonPenalty,Finset.sum_boole] using hc'

theorem static_count_bound {P : List (List ℝ)} (hP : GoodBins P) (hE : EarlyBins P) :
    (P.length : ℝ) ≤ (∑ i∈Finset.range P.length,weight (P.getD i []))+3 := by
  classical
  have hd := Finset.sum_le_sum (s := Finset.range P.length)
    (fun i hi => deficit_step hP hE (Finset.mem_range.mp hi))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hd
  rw [sum_increments] at hd
  simp only [coarseAt,prefixMax,sub_zero] at hd
  have hp := singleton_penalty_sum hP hE
  have hc := coarseAt_le_one hP (i := P.length) le_rfl
  change prefixMax (fun j => 1-(P.getD j []).sum) P.length ≤ 1 at hc
  have hs := Finset.sum_le_sum (s := Finset.range P.length) (fun i _ =>
    show (1 : ℝ) ≤ weight (P.getD i [])+max (1-weight (P.getD i [])) 0 by
      have h := le_max_left (1-weight (P.getD i [])) 0
      linarith)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Finset.sum_add_distrib] at hs
  linarith

end BinPacking.FirstFit.Proof
-- End StaticUpper

-- Begin WeightCapacity

namespace BinPacking.FirstFit.Proof

variable {ι : Type*}

theorem bonus_sum_le (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i∈S, 0 ≤ x i ∧ x i ≤ 1/2) (hs : ∑ i∈S, x i ≤ 1/2) :
    ∑ i∈S, bonus (x i) ≤ 1/10 := by
  classical
  let T := S.filter (fun i => 1/6 < x i)
  have hT : T ⊆ S := Finset.filter_subset _ _
  have he : ∑ i∈S, bonus (x i) = ∑ i∈T, bonus (x i) := by
    symm
    apply Finset.sum_subset hT
    intro i hi hn
    exact bonus_zero (by simpa [T,hi] using hn)
  rw [he]
  by_cases hc : T.card ≤ 1
  · have hh := Finset.sum_le_sum (s := T) (fun i hi => (W_small_bounds (hx i (hT hi)).1 (hx i (hT hi)).2).2.2.2)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    have hc' : (T.card : ℝ) ≤ 1 := by exact_mod_cast hc
    nlinarith
  · have hc' : (2 : ℝ) ≤ T.card := by exact_mod_cast (show 2 ≤ T.card by omega)
    have hh := Finset.sum_le_sum (s := T) (fun i hi => bonus_linear_le (Finset.mem_filter.mp hi).2 (hx i (hT hi)).2)
    have hsum : ∑ i∈T,x i ≤ 1/2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hT (fun i hi _ => (hx i hi).1)).trans hs
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hh
    nlinarith

theorem small_weight_sum (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i∈S, 0 ≤ x i ∧ x i ≤ 1/2) (hs : ∑ i∈S, x i ≤ 1/2) :
    ∑ i∈S, W (x i) ≤ 7/10 := by
  have hb := bonus_sum_le S x hx hs
  have he : (∑ i∈S, W (x i)) = 6/5*(∑ i∈S,x i) + ∑ i∈S,bonus (x i) := by
    simp only [bonus,Finset.sum_sub_distrib,Finset.mul_sum]
    ring
  rw [he]
  linarith

theorem capacity_weight_sum (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i∈S, 0 ≤ x i) (hs : ∑ i∈S, x i ≤ 1) :
    ∑ i∈S, W (x i) ≤ 17/10 := by
  classical
  by_cases h : ∀ i∈S, x i ≤ 1/2
  · have hh := Finset.sum_le_sum (s := S) (fun i hi => (W_small_bounds (hx i hi) (h i hi)).2.1)
    rw [← Finset.mul_sum] at hh
    linarith
  · push Not at h
    obtain ⟨i,hi,hbig⟩ := h
    have hs' : ∑ j∈S.erase i,x j ≤ 1/2 := by
      rw [← Finset.add_sum_erase _ _ hi] at hs
      linarith
    have hx' : ∀ j∈S.erase i,0 ≤ x j ∧ x j ≤ 1/2 := by
      intro j hj
      refine ⟨hx j (Finset.mem_of_mem_erase hj),?_⟩
      exact (Finset.single_le_sum (fun k hk => hx k (Finset.mem_of_mem_erase hk)) hj).trans hs'
    have hh := small_weight_sum (S.erase i) x hx' hs'
    rw [← Finset.add_sum_erase _ _ hi,W_large hbig]
    linarith

theorem capacity_weight {B : List ℝ} (hB : IsList B) (hs : B.sum ≤ 1) :
    weight B ≤ 17/10 := by
  have hh := capacity_weight_sum Finset.univ B.get (fun i _ => (hB _ (List.get_mem ..)).1.le)
    (by simpa using hs)
  simpa [weight] using hh

end BinPacking.FirstFit.Proof
-- End WeightCapacity

-- Begin OptimumBasic

namespace BinPacking.FirstFit.Proof

def FeasiblePacking (L : List ℝ) (b : ℕ) : Prop :=
  ∃ f : Fin L.length → Fin b, ∀ j, ∑ i ∈ Finset.univ.filter (fun i => f i=j), L.get i ≤ 1

theorem self_packing (L : List ℝ) (hL : IsList L) : FeasiblePacking L L.length := by
  classical
  refine ⟨id,?_⟩
  intro j
  simpa [Finset.sum_filter] using (hL (L.get j) (List.get_mem ..)).2

theorem optimum_exists (L : List ℝ) (hL : IsList L) : FeasiblePacking L (optBins L) := by
  change sInf {b : ℕ | FeasiblePacking L b} ∈ {b : ℕ | FeasiblePacking L b}
  exact Nat.sInf_mem ⟨L.length,self_packing L hL⟩

theorem optimum_le {L : List ℝ} {b : ℕ} (h : FeasiblePacking L b) : optBins L ≤ b :=
  Nat.sInf_le h

@[simp] theorem optimum_nil : optBins []=0 := by
  apply Nat.eq_zero_of_le_zero
  apply optimum_le
  refine ⟨Fin.elim0,?_⟩
  intro j
  exact Fin.elim0 j

theorem optimum_le_length (L : List ℝ) (hL : IsList L) : optBins L ≤ L.length :=
  optimum_le (self_packing L hL)

end BinPacking.FirstFit.Proof
-- End OptimumBasic

-- Begin IndexPermutation

namespace BinPacking.FirstFit.Proof

def finConsEquiv {n m : ℕ} (e : Fin n ≃ Fin m) : Fin (n+1) ≃ Fin (m+1) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv := by intro i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

@[simp] theorem finConsEquiv_zero {n m : ℕ} (e : Fin n ≃ Fin m) : finConsEquiv e 0=0 := rfl
@[simp] theorem finConsEquiv_succ {n m : ℕ} (e : Fin n ≃ Fin m) (i : Fin n) :
    finConsEquiv e i.succ=(e i).succ := rfl

theorem perm_index_equiv {α : Type*} {L K : List α} (h : L.Perm K) :
    ∃ e : Fin L.length ≃ Fin K.length, ∀ i, K.get (e i)=L.get i := by
  induction h with
  | nil => exact ⟨Equiv.refl _,fun _ => rfl⟩
  | cons a h ih =>
    obtain ⟨e,he⟩ := ih
    refine ⟨finConsEquiv e,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simpa using he j
  | swap a b L =>
    refine ⟨Equiv.swap 0 1,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · have h0 : k.succ.succ ≠ (0 : Fin (L.length+2)) := by simp
        have h1 : k.succ.succ ≠ (1 : Fin (L.length+2)) := by
          intro hh
          have hv := congrArg Fin.val hh
          simp at hv
        simp [Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e,he⟩ := ih₁
    obtain ⟨f,hf⟩ := ih₂
    exact ⟨e.trans f,fun i => (hf (e i)).trans (he i)⟩

end BinPacking.FirstFit.Proof
-- End IndexPermutation

-- Begin OptimumPermutation

namespace BinPacking.FirstFit.Proof

theorem feasible_of_perm {L K : List ℝ} (h : L.Perm K) {b : ℕ}
    (hp : FeasiblePacking K b) : FeasiblePacking L b := by
  classical
  obtain ⟨e,he⟩ := perm_index_equiv h
  obtain ⟨f,hf⟩ := hp
  refine ⟨fun i => f (e i),?_⟩
  intro j
  have hs : (∑ i : Fin L.length, if f (e i)=j then L.get i else 0) =
      ∑ k : Fin K.length, if f k=j then K.get k else 0 := by
    apply Fintype.sum_equiv e
    intro i
    rw [he]
  simpa only [← Finset.sum_filter] using hs.trans_le (by simpa only [Finset.sum_filter] using hf j)

theorem optimum_perm {L K : List ℝ} (h : L.Perm K) (hL : IsList L) : optBins L=optBins K := by
  have hK : IsList K := fun a ha => hL a (h.mem_iff.mpr ha)
  apply Nat.le_antisymm
  · exact optimum_le (feasible_of_perm h (optimum_exists K hK))
  · exact optimum_le (feasible_of_perm h.symm (optimum_exists L hL))

end BinPacking.FirstFit.Proof
-- End OptimumPermutation

-- Begin AssignmentBasic

namespace BinPacking.FirstFit.Proof

theorem total_mass_le_bins {L : List ℝ} {b : ℕ} (h : FeasiblePacking L b) :
    L.sum ≤ (b : ℝ) := by
  classical
  obtain ⟨f,hf⟩ := h
  have hs : (∑ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i=j), L.get i) = L.sum := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [← hs]
  calc
    _ ≤ ∑ _j : Fin b, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hf j)
    _ = b := by simp

theorem volume_le_optimum (L : List ℝ) (hL : IsList L) : L.sum ≤ (optBins L : ℝ) :=
  total_mass_le_bins (optimum_exists L hL)

theorem feasible_cons_bin (B L : List ℝ) {b : ℕ} (hB : B.sum ≤ 1)
    (hL : FeasiblePacking L b) : FeasiblePacking (B++L) (b+1) := by
  classical
  obtain ⟨f,hf⟩ := hL
  let g : Fin (B.length+L.length) → Fin (b+1) :=
    Fin.addCases (fun _ => 0) (fun i => (f i).succ)
  refine ⟨fun i => g (Fin.cast (List.length_append (as := B) (bs := L)) i),?_⟩
  intro j
  simp only [Finset.sum_filter]
  change (∑ i : Fin (B++L).length, if g (Fin.cast (List.length_append (as := B) (bs := L)) i)=j then (B++L).get i else 0) ≤ 1
  have he := Fintype.sum_equiv (finCongr (List.length_append (as := B) (bs := L)))
    (fun i : Fin (B++L).length => if g (Fin.cast (List.length_append (as := B) (bs := L)) i)=j then (B++L).get i else 0)
    (fun i : Fin (B.length+L.length) => if g i=j then (B++L)[i.val]'(by simp only [List.length_append]; exact i.isLt) else 0)
    (by intro i; rfl)
  rw [he,Fin.sum_univ_add]
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [g,List.getElem_append] using hB
  · simpa [g,List.getElem_append,Finset.sum_filter,Ne.symm (Fin.succ_ne_zero k)] using hf k

theorem feasible_flatten (P : List (List ℝ)) (h : ∀ B∈P, B.sum ≤ 1) :
    FeasiblePacking P.flatten P.length := by
  induction P with
  | nil => exact ⟨Fin.elim0,fun j => Fin.elim0 j⟩
  | cons B P ih =>
    exact feasible_cons_bin B P.flatten (h B (by simp)) (ih (fun C hC => h C (by simp [hC])))

theorem feasible_of_perm_flatten {P : List (List ℝ)} {L : List ℝ}
    (h : P.flatten.Perm L) (hP : ∀ B∈P, B.sum≤1) : FeasiblePacking L P.length :=
  feasible_of_perm h.symm (feasible_flatten P hP)

end BinPacking.FirstFit.Proof
-- End AssignmentBasic

-- Begin WeightAccounting

namespace BinPacking.FirstFit.Proof

theorem weight_le_optimum (L : List ℝ) (hL : IsList L) :
    weight L ≤ 17/10*(optBins L : ℝ) := by
  classical
  obtain ⟨f,hf⟩ := optimum_exists L hL
  have hh : ∀ j : Fin (optBins L),
      ∑ i ∈ Finset.univ.filter (fun i => f i=j),W (L.get i) ≤ 17/10 := by
    intro j
    exact capacity_weight_sum _ L.get (fun i _ => (hL _ (List.get_mem ..)).1.le) (hf j)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh j)
  simp only [Finset.sum_filter] at hs
  rw [Finset.sum_comm] at hs
  simpa [weight,mul_comm] using hs

theorem run_weight_total (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (L : List ℝ) :
    (∑ j∈Finset.range (run choose L).length,weight ((run choose L).getD j []))=weight L := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [weight,run_measure choose hr L W,Finset.sum_filter]
  rw [Finset.sum_comm]
  have he : ∀ i : Fin L.length,
      (∑ j : Fin (run choose L).length,if binOf choose L i=j.val then W (L.get i) else 0)=W (L.get i) := by
    intro i
    let j : Fin (run choose L).length := ⟨binOf choose L i,binOf_lt_run_length choose hr L i⟩
    have hh : ∀ k : Fin (run choose L).length, binOf choose L i=k.val ↔ k=j := by
      intro k
      exact ⟨fun h => Fin.ext h.symm,fun h => by subst k; rfl⟩
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,if_pos]
  simp only [he]
  simp

end BinPacking.FirstFit.Proof
-- End WeightAccounting

-- Begin NativeUpper

namespace BinPacking.FirstFit.Proof

theorem native_upper (choose : List (List ℝ) → ℝ → ℕ) (hr : ChoiceRule choose)
    (he : EarlyRule choose) (L : List ℝ) (hL : IsList L) :
    ((run choose L).length : ℝ) ≤ 17/10*(optBins L : ℝ)+3 := by
  have hs := static_count_bound (run_good choose hr L hL) (run_separated_early choose hr he L hL).2
  rw [run_weight_total choose hr L] at hs
  linarith [weight_le_optimum L hL]

theorem ff_upper (L : List ℝ) (hL : IsList L) : (FF L : ℝ) ≤ 17/10*(optBins L : ℝ)+3 :=
  native_upper ffChoice ff_choice_rule ff_early_rule L hL

theorem bf_upper (L : List ℝ) (hL : IsList L) : (BF L : ℝ) ≤ 17/10*(optBins L : ℝ)+3 :=
  native_upper bfChoice bf_choice_rule bf_early_rule L hL

end BinPacking.FirstFit.Proof
-- End NativeUpper

-- Begin RatioSqueeze

namespace BinPacking.FirstFit.Proof

open Filter
open scoped Topology

theorem ratio_tendsto_of_bounds (A : List ℝ → ℕ)
    (hu : ∀ L, IsList L → (A L : ℝ) ≤ 17/10*(optBins L : ℝ)+3)
    (hl : ∀ k : ℕ, 1≤k → ∃ L, IsList L ∧ optBins L=k ∧ 17/10*(k : ℝ)-8 ≤ A L) :
    Tendsto (fun k : ℕ => ⨆ (L : List ℝ) (_ : IsList L) (_ : optBins L=k),
      (A L : ENNReal)/(k : ENNReal)) atTop (nhds ((17 : ENNReal)/10)) := by
  have hz : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun k : ℕ => ENNReal.ofReal (17/10-8/(k : ℝ))) atTop
      (nhds ((17 : ENNReal)/10)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (17/10 : ℝ))).sub ((tendsto_const_nhds (x := (8 : ℝ))).mul hz))
    simpa only [Function.comp_def,mul_zero,sub_zero,← div_eq_mul_inv,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<10),ENNReal.ofReal_ofNat] using hh
  have hupp : Tendsto (fun k : ℕ => ENNReal.ofReal (17/10+3/(k : ℝ))) atTop
      (nhds ((17 : ENNReal)/10)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x := (17/10 : ℝ))).add ((tendsto_const_nhds (x := (3 : ℝ))).mul hz))
    simpa only [Function.comp_def,mul_zero,add_zero,← div_eq_mul_inv,
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<10),ENNReal.ofReal_ofNat] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
    obtain ⟨L,hL,he,hb⟩ := hl k hk
    have hd : 17/10-8/(k : ℝ) ≤ (A L : ℝ)/k := by
      apply (le_div_iff₀ hk').mpr
      field_simp
      nlinarith
    have hh := ENNReal.ofReal_le_ofReal hd
    rw [ENNReal.ofReal_div_of_pos hk'] at hh
    simp only [ENNReal.ofReal_natCast] at hh
    exact hh.trans (le_iSup_of_le L (le_iSup_of_le hL (le_iSup_of_le he le_rfl)))
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
    refine iSup_le fun L => iSup_le fun hL => iSup_le fun he => ?_
    have hh := hu L hL
    rw [he] at hh
    have hd : (A L : ℝ)/k ≤ 17/10+3/(k : ℝ) := by
      apply (div_le_iff₀ hk').mpr
      field_simp
      nlinarith
    have h := ENNReal.ofReal_le_ofReal hd
    rw [ENNReal.ofReal_div_of_pos hk'] at h
    simpa only [ENNReal.ofReal_natCast] using h

end BinPacking.FirstFit.Proof
-- End RatioSqueeze

-- Begin LowerRun

namespace BinPacking.FirstFit.Proof

lemma choice_new_of_no_fit (choose : List (List ℝ) → ℝ → ℕ) (hc : ChoiceRule choose)
    (B : List (List ℝ)) (a : ℝ) (hn : ∀C∈B,1<C.sum+a) : choose B a=B.length := by
  have hh := hc B a
  by_contra he
  have hl : choose B a<B.length := by omega
  have hf := hh.2.1 hl
  have hm : B.getD (choose B a) []∈B := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  linarith [hn _ hm]

lemma choice_last_of_unique (choose : List (List ℝ) → ℝ → ℕ) (hc : ChoiceRule choose)
    (B : List (List ℝ)) (A : List ℝ) (a : ℝ)
    (hn : ∀C∈B,1<C.sum+a) (hf : A.sum+a≤1) : choose (B++[A]) a=B.length := by
  have hh := hc (B++[A]) a
  by_cases hl : choose (B++[A]) a<(B++[A]).length
  · by_contra he
    have hlt : choose (B++[A]) a<B.length := by simp only [List.length_append,List.length_singleton] at hl; omega
    have hfit := hh.2.1 hl
    rw [List.getD_eq_getElem _ _ hl,List.getElem_append_left hlt,← List.getD_eq_getElem _ _ hlt] at hfit
    have hm : B.getD (choose (B++[A]) a) []∈B := by
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    linarith [hn _ hm]
  · have he : choose (B++[A]) a=(B++[A]).length := by omega
    have hn' := hh.2.2 he A (by simp)
    linarith

lemma placeAt_last (B : List (List ℝ)) (A : List ℝ) (a : ℝ) :
    placeAt (B++[A]) B.length a=B++[A++[a]] := by
  unfold placeAt
  rw [if_pos (by simp)]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_mapIdx]
    by_cases h : i<B.length
    · rw [List.getElem_append_left h,List.getElem_append_left h,if_neg (by omega)]
    · have he : i=B.length := by simp only [List.length_mapIdx,List.length_append,List.length_singleton] at hi; omega
      subst i
      simp

lemma fold_active_group (choose : List (List ℝ) → ℝ → ℕ) (hc : ChoiceRule choose)
    (B : List (List ℝ)) (A K : List ℝ)
    (hn : ∀a∈K,∀C∈B,1<C.sum+a) (hp : ∀a∈K,0≤a)
    (hs : (A++K).sum≤1) :
    K.foldl (fun bins a=>placeAt bins (choose bins a) a) (B++[A])=B++[A++K] := by
  induction K generalizing A with
  | nil => simp
  | cons a K ih =>
    have hk : 0≤K.sum := List.sum_nonneg (fun x hx=>hp x (by simp [hx]))
    have hfit : A.sum+a≤1 := by simp only [List.sum_append,List.sum_cons] at hs; linarith
    rw [List.foldl_cons,choice_last_of_unique choose hc B A a (hn a (by simp)) hfit,placeAt_last]
    rw [ih (A++[a]) (fun x hx=>hn x (by simp [hx])) (fun x hx=>hp x (by simp [hx]))]
    · simp
    · simpa [List.sum_append,List.sum_cons,add_assoc] using hs

lemma fold_group (choose : List (List ℝ) → ℝ → ℕ) (hc : ChoiceRule choose)
    (B : List (List ℝ)) (A : List ℝ) (hne : A≠[])
    (hn : ∀a∈A,∀C∈B,1<C.sum+a) (hp : ∀a∈A,0≤a) (hs : A.sum≤1) :
    A.foldl (fun bins a=>placeAt bins (choose bins a) a) B=B++[A] := by
  cases A with
  | nil => exact (hne rfl).elim
  | cons a K =>
    rw [List.foldl_cons,choice_new_of_no_fit choose hc B a (hn a (by simp))]
    rw [placeAt,if_neg (Nat.lt_irrefl _)]
    simpa using fold_active_group choose hc B [a] K (fun x hx=>hn x (by simp [hx]))
      (fun x hx=>hp x (by simp [hx])) (by simpa using hs)

lemma run_groups (choose : List (List ℝ) → ℝ → ℕ) (hc : ChoiceRule choose)
    (P : List (List ℝ)) (hne : ∀A∈P,A≠[]) (hp : ∀A∈P,∀a∈A,0≤a)
    (hs : ∀A∈P,A.sum≤1)
    (hsep : ∀i j (hi:i<P.length) (hj:j<P.length),i<j → ∀a∈P[j],1<P[i].sum+a) :
    run choose P.flatten=P := by
  induction P using List.reverseRecOn with
  | nil => simp
  | append_singleton P A ih =>
    have hP : ∀i j (hi:i<P.length) (hj:j<P.length),i<j → ∀a∈P[j],1<P[i].sum+a := by
      intro i j hi hj hij a ha
      have hh := hsep i j (by simp; omega) (by simp; omega) hij a (by simpa only [List.getElem_append_left hj] using ha)
      rw [List.getElem_append_left hi] at hh
      exact hh
    rw [List.flatten_append,List.flatten_singleton,run_append,
      ih (fun C hC=>hne C (by simp [hC])) (fun C hC=>hp C (by simp [hC]))
        (fun C hC=>hs C (by simp [hC])) hP]
    apply fold_group choose hc P A (hne A (by simp)) _ (hp A (by simp)) (hs A (by simp))
    intro a ha C hC
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hC
    have hh := hsep i P.length (by simp; omega) (by simp) hi a (by simpa using ha)
    rw [List.getElem_append_left hi] at hh
    exact hh

end BinPacking.FirstFit.Proof
-- End LowerRun

-- Begin LowerFamily

namespace BinPacking.FirstFit.Proof

noncomputable def lowerDelta (i : ℕ) : ℝ := 1/(10000*18^i)
noncomputable def lowerA (t : ℝ) : List (List ℝ) :=
  [[1/6+33*t,1/6-3*t,1/6-7*t,1/6-7*t,1/6-13*t],
   [1/6+9*t,1/6-2*t,1/6-2*t,1/6-2*t,1/6-2*t]]
noncomputable def lowerB (t : ℝ) : List (List ℝ) :=
  [[1/3+46*t,1/3-34*t],[1/3+6*t,1/3+6*t],[1/3+12*t,1/3-10*t],
   [1/3+t,1/3+t],[1/3+t,1/3+t]]
noncomputable def lowerPacking (r : ℕ) : List (List ℝ) :=
  (List.range r).flatMap (fun i=>lowerA (lowerDelta i)) ++
  (List.range r).flatMap (fun i=>lowerB (lowerDelta i)) ++
  List.replicate (10*r) [1/2+lowerDelta r]
noncomputable def lowerList (r : ℕ) : List ℝ := (lowerPacking r).flatten

def SeparatedGroups (P : List (List ℝ)) : Prop :=
  P.Pairwise (fun A B=>∀a∈B,1<A.sum+a)

lemma lowerDelta_pos (i : ℕ) : 0<lowerDelta i := by unfold lowerDelta; positivity
lemma lowerDelta_le (i : ℕ) : lowerDelta i≤1/10000 := by
  unfold lowerDelta
  apply one_div_le_one_div_of_le (by norm_num)
  have h : (1:ℝ)≤18^i := one_le_pow₀ (by norm_num)
  nlinarith
lemma lowerDelta_succ (i : ℕ) : lowerDelta (i+1)=lowerDelta i/18 := by
  unfold lowerDelta
  rw [pow_succ]
  field_simp
lemma lowerDelta_mono : Antitone lowerDelta := by
  apply antitone_nat_of_succ_le
  intro i
  rw [lowerDelta_succ]
  linarith [lowerDelta_pos i]
lemma lowerDelta_gap {i j : ℕ} (h : i<j) : 18*lowerDelta j≤lowerDelta i := by
  have hh := lowerDelta_mono (Nat.succ_le_of_lt h)
  rw [lowerDelta_succ] at hh
  linarith

lemma lowerA_nonempty (t : ℝ) : ∀A∈lowerA t,A≠[] := by simp [lowerA]
lemma lowerB_nonempty (t : ℝ) : ∀A∈lowerB t,A≠[] := by simp [lowerB]

lemma lowerA_items (t : ℝ) (ht : 0<t) (htb : t≤1/10000) :
    ∀A∈lowerA t,∀a∈A,0<a ∧ a≤1 ∧ 1/6-13*t≤a ∧ a≤1/6+33*t := by
  intro A hA a ha
  simp only [lowerA,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl|rfl
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl
  all_goals repeat' constructor
  all_goals linarith

lemma lowerB_items (t : ℝ) (ht : 0<t) (htb : t≤1/10000) :
    ∀A∈lowerB t,∀a∈A,0<a ∧ a≤1 ∧ 1/3-34*t≤a ∧ a≤1/3+46*t := by
  intro A hA a ha
  simp only [lowerB,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  all_goals rcases ha with rfl|rfl
  all_goals repeat' constructor
  all_goals linarith

lemma lowerA_levels (t : ℝ) (ht : 0<t) (htb : t≤1/10000) :
    ∀A∈lowerA t,5/6+t≤A.sum ∧ A.sum≤1 := by
  intro A hA
  simp only [lowerA,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl|rfl
  all_goals simp only [List.sum_cons,List.sum_nil]; constructor <;> linarith

lemma lowerB_levels (t : ℝ) (ht : 0<t) (htb : t≤1/10000) :
    ∀A∈lowerB t,2/3+2*t≤A.sum ∧ A.sum≤1 := by
  intro A hA
  simp only [lowerB,List.mem_cons,List.not_mem_nil,or_false] at hA
  rcases hA with rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.sum_cons,List.sum_nil]; constructor <;> linarith

lemma lowerA_separated (t : ℝ) (ht : 0<t) : SeparatedGroups (lowerA t) := by
  norm_num [SeparatedGroups,lowerA,List.pairwise_cons]
  repeat' constructor
  all_goals linarith

lemma lowerB_separated (t : ℝ) (ht : 0<t) : SeparatedGroups (lowerB t) := by
  norm_num [SeparatedGroups,lowerB,List.pairwise_cons]
  repeat' constructor
  all_goals linarith

end BinPacking.FirstFit.Proof
-- End LowerFamily

-- Begin LowerValues

namespace BinPacking.FirstFit.Proof

noncomputable def aValue (i : ℕ) : Fin 10→ℝ :=
  ![1/6+33*lowerDelta i,1/6-3*lowerDelta i,1/6-7*lowerDelta i,
    1/6-7*lowerDelta i,1/6-13*lowerDelta i,1/6+9*lowerDelta i,
    1/6-2*lowerDelta i,1/6-2*lowerDelta i,1/6-2*lowerDelta i,1/6-2*lowerDelta i]
noncomputable def bValue (i : ℕ) : Fin 10→ℝ :=
  ![1/3+46*lowerDelta i,1/3-34*lowerDelta i,1/3+6*lowerDelta i,
    1/3+6*lowerDelta i,1/3+12*lowerDelta i,1/3-10*lowerDelta i,
    1/3+lowerDelta i,1/3+lowerDelta i,1/3+lowerDelta i,1/3+lowerDelta i]

lemma lowerA_flatten (i : ℕ) : (lowerA (lowerDelta i)).flatten=List.ofFn (aValue i) := by
  rfl
lemma lowerB_flatten (i : ℕ) : (lowerB (lowerDelta i)).flatten=List.ofFn (bValue i) := by
  rfl

noncomputable def lowerPartner (r : ℕ) : Equiv.Perm (Fin r × Fin 10) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)).trans
    (Equiv.prodCongrLeft (fun j : Fin 10=>if j=0 then finRotate r else Equiv.refl _))

lemma lowerPartner_zero {r : ℕ} (i : Fin r) : lowerPartner r (i,0)=(i,1) := by
  simp [lowerPartner,Equiv.prodCongrLeft_apply]
lemma lowerPartner_one {r : ℕ} (i : Fin r) : lowerPartner r (i,1)=(finRotate r i,0) := by
  simp [lowerPartner,Equiv.prodCongrLeft_apply]
lemma lowerPartner_other {r : ℕ} (i : Fin r) (j : Fin 10) (hj0:j≠0) (hj1:j≠1) :
    lowerPartner r (i,j)=(i,j) := by
  simp [lowerPartner,Equiv.prodCongrLeft_apply,Equiv.swap_apply_of_ne_of_ne hj0 hj1,hj0]

lemma lower_triple_bound {r : ℕ} (hr : 0<r) (i : Fin r) (j : Fin 10)
    (hbad : ¬(i.val=r-1 ∧ j=1)) :
    aValue i j + bValue (lowerPartner r (i,j)).1 (lowerPartner r (i,j)).2 +
      (1/2+lowerDelta r) ≤ 1 := by
  have hd := lowerDelta_mono (Nat.le_of_lt i.isLt)
  by_cases hj0 : j=0
  · subst j
    rw [lowerPartner_zero]
    simp only [aValue,bValue,Matrix.cons_val_zero,Matrix.cons_val_one]
    linarith
  by_cases hj1 : j=1
  · subst j
    rw [lowerPartner_one]
    have hi : i.val+1<r := by omega
    have he : (finRotate r i).val=i.val+1 := by
      cases r with
      | zero => omega
      | succ r =>
        have hri : i.val<r := by omega
        have h:=finRotate_of_lt hri
        simpa using congrArg Fin.val h
    simp only [aValue,bValue,Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [he,lowerDelta_succ]
    have hsmall := lowerDelta_mono (Nat.le_of_lt hi)
    rw [lowerDelta_succ] at hsmall
    linarith
  · rw [lowerPartner_other i j hj0 hj1]
    fin_cases j <;> norm_num [aValue,bValue] at * <;> linarith

lemma lower_wrap_bound (r : ℕ) : aValue r 1+bValue 0 0≤1 := by
  have h := lowerDelta_pos r
  have hz : lowerDelta 0 = 1/10000 := by norm_num [lowerDelta]
  simp only [aValue,bValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hz]
  linarith

end BinPacking.FirstFit.Proof
-- End LowerValues

-- Begin LowerSlots

namespace BinPacking.FirstFit.Proof

noncomputable def lowerSlots (r : ℕ) : List (Fin r × Fin 10) :=
  (List.finRange r).flatMap (fun i => (List.finRange 10).map (fun j => (i,j)))

lemma mem_lowerSlots {r : ℕ} (s : Fin r × Fin 10) : s ∈ lowerSlots r := by
  simp [lowerSlots,List.mem_flatMap]

lemma lowerSlots_nodup (r : ℕ) : (lowerSlots r).Nodup := by
  classical
  simp only [lowerSlots,List.nodup_flatMap]
  constructor
  · intro i hi
    exact (List.nodup_finRange 10).map (fun _ _ h => (Prod.mk.inj h).2)
  · apply (List.nodup_finRange r).imp
    intro i j hij
    simp only [List.disjoint_left,List.mem_map]
    rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
    exact hij (Prod.mk.inj he.symm).1

lemma lowerSlots_length (r : ℕ) : (lowerSlots r).length=10*r := by
  simp [lowerSlots,List.length_flatMap,List.map_const',Nat.mul_comm]

lemma lowerPartner_perm (r : ℕ) : ((lowerSlots r).map (lowerPartner r)).Perm (lowerSlots r) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((lowerSlots_nodup r).map (lowerPartner r).injective)
    (lowerSlots_nodup r)).mpr
  intro s
  simp only [mem_lowerSlots,iff_true,List.mem_map]
  exact ⟨(lowerPartner r).symm s,True.intro,(lowerPartner r).apply_symm_apply s⟩

lemma finRange_val (r : ℕ) : (List.finRange r).map Fin.val=List.range r := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

lemma lower_flatten_flatMap {α β : Type*} (L : List α) (f : α→List (List β)) :
    (L.flatMap f).flatten=L.flatMap (fun a=>(f a).flatten) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

lemma lowerSlots_a (r : ℕ) :
    (lowerSlots r).map (fun s => aValue s.1 s.2) =
    ((List.range r).flatMap (fun i => lowerA (lowerDelta i))).flatten := by
  rw [← finRange_val r]
  simp only [lowerSlots,List.map_flatMap,List.map_map,List.flatMap_map,
    lower_flatten_flatMap,lowerA_flatten,List.ofFn_eq_map]
  rfl

lemma lowerSlots_b (r : ℕ) :
    (lowerSlots r).map (fun s => bValue s.1 s.2) =
    ((List.range r).flatMap (fun i => lowerB (lowerDelta i))).flatten := by
  rw [← finRange_val r]
  simp only [lowerSlots,List.map_flatMap,List.map_map,List.flatMap_map,
    lower_flatten_flatMap,lowerB_flatten,List.ofFn_eq_map]
  rfl

end BinPacking.FirstFit.Proof
-- End LowerSlots

-- Begin LowerSeparation

namespace BinPacking.FirstFit.Proof

lemma separated_flat_range (f : ℕ→List (List ℝ)) (r : ℕ)
    (hf : ∀i<r,SeparatedGroups (f i))
    (hcross : ∀i j,i<j → j<r → ∀A∈f i,∀B∈f j,∀a∈B,1<A.sum+a) :
    SeparatedGroups ((List.range r).flatMap f) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun i hi=>hf i (List.mem_range.mp hi),?_⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [List.length_range] at hi hj
  simpa only [List.getElem_range] using hcross i j hij hj

lemma lowerA_all_separated (r : ℕ) :
    SeparatedGroups ((List.range r).flatMap (fun i=>lowerA (lowerDelta i))) := by
  apply separated_flat_range
  · intro i _
    exact lowerA_separated _ (lowerDelta_pos i)
  · intro i j hij _ A hA B hB a ha
    have h1 := (lowerA_levels _ (lowerDelta_pos i) (lowerDelta_le i) A hA).1
    have h2 := (lowerA_items _ (lowerDelta_pos j) (lowerDelta_le j) B hB a ha).2.2.1
    have hg := lowerDelta_gap hij
    linarith [lowerDelta_pos j]

lemma lowerB_all_separated (r : ℕ) :
    SeparatedGroups ((List.range r).flatMap (fun i=>lowerB (lowerDelta i))) := by
  apply separated_flat_range
  · intro i _
    exact lowerB_separated _ (lowerDelta_pos i)
  · intro i j hij _ A hA B hB a ha
    have h1 := (lowerB_levels _ (lowerDelta_pos i) (lowerDelta_le i) A hA).1
    have h2 := (lowerB_items _ (lowerDelta_pos j) (lowerDelta_le j) B hB a ha).2.2.1
    have hg := lowerDelta_gap hij
    linarith [lowerDelta_pos j]

lemma lowerPacking_separated (r : ℕ) : SeparatedGroups (lowerPacking r) := by
  unfold lowerPacking
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨lowerA_all_separated r,lowerB_all_separated r,?_⟩
    intro A hA B hB a ha
    obtain ⟨i,_,hA⟩ := List.mem_flatMap.mp hA
    obtain ⟨j,_,hB⟩ := List.mem_flatMap.mp hB
    have h1 := (lowerA_levels _ (lowerDelta_pos i) (lowerDelta_le i) A hA).1
    have h2 := (lowerB_items _ (lowerDelta_pos j) (lowerDelta_le j) B hB a ha).2.2.1
    linarith [lowerDelta_pos i,lowerDelta_le j]
  · apply List.pairwise_replicate.mpr
    right
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    simp only [List.sum_cons,List.sum_nil]
    linarith [lowerDelta_pos r]
  · intro A hA B hB a ha
    have hBeq : B=[1/2+lowerDelta r] := (List.mem_replicate.mp hB).2
    subst B
    simp only [List.mem_singleton] at ha
    subst a
    rcases List.mem_append.mp hA with hA|hA
    · obtain ⟨i,_,hA⟩ := List.mem_flatMap.mp hA
      have h1 := (lowerA_levels _ (lowerDelta_pos i) (lowerDelta_le i) A hA).1
      linarith [lowerDelta_pos r,lowerDelta_pos i]
    · obtain ⟨i,_,hA⟩ := List.mem_flatMap.mp hA
      have h1 := (lowerB_levels _ (lowerDelta_pos i) (lowerDelta_le i) A hA).1
      linarith [lowerDelta_pos r,lowerDelta_pos i]

end BinPacking.FirstFit.Proof
-- End LowerSeparation

-- Begin LowerPacking

namespace BinPacking.FirstFit.Proof

lemma mem_lowerPacking {r : ℕ} {A : List ℝ} (h : A∈lowerPacking r) :
    (∃i<r,A∈lowerA (lowerDelta i)) ∨ (∃i<r,A∈lowerB (lowerDelta i)) ∨
      A=[1/2+lowerDelta r] := by
  simp only [lowerPacking,List.mem_append,List.mem_flatMap,List.mem_range,List.mem_replicate] at h
  rcases h with (h|h)|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h.2)

lemma lowerPacking_nonempty (r : ℕ) : ∀A∈lowerPacking r,A≠[] := by
  intro A hA
  rcases mem_lowerPacking hA with ⟨i,_,h⟩|⟨i,_,h⟩|rfl
  · exact lowerA_nonempty _ A h
  · exact lowerB_nonempty _ A h
  · simp

lemma lowerPacking_items (r : ℕ) : ∀A∈lowerPacking r,∀a∈A,0<a ∧ a≤1 := by
  intro A hA a ha
  rcases mem_lowerPacking hA with ⟨i,_,h⟩|⟨i,_,h⟩|rfl
  · have hh:=lowerA_items _ (lowerDelta_pos i) (lowerDelta_le i) A h a ha
    exact ⟨hh.1,hh.2.1⟩
  · have hh:=lowerB_items _ (lowerDelta_pos i) (lowerDelta_le i) A h a ha
    exact ⟨hh.1,hh.2.1⟩
  · simp only [List.mem_singleton] at ha
    subst a
    constructor <;> linarith [lowerDelta_pos r,lowerDelta_le r]

lemma lowerPacking_capacity (r : ℕ) : ∀A∈lowerPacking r,A.sum≤1 := by
  intro A hA
  rcases mem_lowerPacking hA with ⟨i,_,h⟩|⟨i,_,h⟩|rfl
  · exact (lowerA_levels _ (lowerDelta_pos i) (lowerDelta_le i) A h).2
  · exact (lowerB_levels _ (lowerDelta_pos i) (lowerDelta_le i) A h).2
  · simp only [List.sum_cons,List.sum_nil]
    linarith [lowerDelta_le r]

lemma lowerList_valid (r : ℕ) : IsList (lowerList r) := by
  intro a ha
  obtain ⟨A,hA,ha⟩ := List.mem_flatten.mp ha
  exact lowerPacking_items r A hA a ha

lemma run_lowerList (choose : List (List ℝ)→ℝ→ℕ) (hc : ChoiceRule choose) (r : ℕ) :
    run choose (lowerList r)=lowerPacking r := by
  apply run_groups choose hc _ (lowerPacking_nonempty r)
    (fun A hA a ha=>(lowerPacking_items r A hA a ha).1.le) (lowerPacking_capacity r)
  exact List.pairwise_iff_getElem.mp (lowerPacking_separated r)

lemma lowerPacking_length (r : ℕ) : (lowerPacking r).length=17*r := by
  simp [lowerPacking,List.length_flatMap,lowerA,lowerB]
  omega

lemma lower_counts (r : ℕ) : FF (lowerList r)=17*r ∧ BF (lowerList r)=17*r := by
  constructor
  · change (run ffChoice (lowerList r)).length=17*r
    rw [run_lowerList _ ff_choice_rule,lowerPacking_length]
  · change (run bfChoice (lowerList r)).length=17*r
    rw [run_lowerList _ bf_choice_rule,lowerPacking_length]

lemma lower_sum_flatMap {α : Type*} (L : List α) (f : α→List ℝ) :
    (L.flatMap f).sum=(L.map (fun a=>(f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma lowerList_mass (r : ℕ) : (lowerList r).sum=
    10*(r:ℝ)+34*((List.range r).map lowerDelta).sum+10*r*lowerDelta r := by
  have hA (t : ℝ) : ((lowerA t).map List.sum).sum=5/3+4*t := by
    simp [lowerA]
    ring
  have hB (t : ℝ) : ((lowerB t).map List.sum).sum=10/3+30*t := by
    simp [lowerB]
    ring
  simp only [lowerList,lowerPacking,List.sum_flatten,List.map_append,List.sum_append,
    List.map_flatMap,lower_sum_flatMap,hA,hB,List.map_replicate,
    List.sum_replicate,List.sum_cons,List.sum_nil,add_zero,nsmul_eq_mul]
  rw [List.sum_map_add,List.sum_map_add,List.sum_map_mul_left,List.sum_map_mul_left]
  simp only [List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma lowerList_mass_gt {r : ℕ} (hr : 0<r) : 10*(r:ℝ)<(lowerList r).sum := by
  rw [lowerList_mass]
  have hs : 0≤((List.range r).map lowerDelta).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hx; exact (lowerDelta_pos i).le)
  have hpos : 0<(r:ℝ) := by exact_mod_cast hr
  nlinarith [lowerDelta_pos r]

end BinPacking.FirstFit.Proof
-- End LowerPacking

-- Begin LowerOptimal

namespace BinPacking.FirstFit.Proof

noncomputable def lowerGoodGroups (r : ℕ) (s : Fin r × Fin 10) : List (List ℝ) :=
  let a := aValue s.1 s.2
  let b := bValue (lowerPartner r s).1 (lowerPartner r s).2
  let c := 1/2+lowerDelta r
  if s.1.val=r-1 ∧ s.2=1 then [[a,b],[c]] else [[a,b,c]]

noncomputable def lowerOptPacking (r : ℕ) : List (List ℝ) :=
  (lowerSlots r).flatMap (lowerGoodGroups r)

lemma lowerGoodGroups_flatten (r : ℕ) (s : Fin r × Fin 10) :
    (lowerGoodGroups r s).flatten =
      [aValue s.1 s.2,bValue (lowerPartner r s).1 (lowerPartner r s).2,1/2+lowerDelta r] := by
  unfold lowerGoodGroups
  split <;> simp

lemma lowerOpt_capacity {r : ℕ} (hr : 0<r) : ∀B∈lowerOptPacking r,B.sum≤1 := by
  intro B hB
  obtain ⟨s,hs,hB⟩ := List.mem_flatMap.mp hB
  unfold lowerGoodGroups at hB
  split at hB
  · rename_i hbad
    rcases hbad with ⟨hi,hj⟩
    rcases s with ⟨i,j⟩
    dsimp at *
    subst j
    rw [lowerPartner_one] at hB
    have he : (finRotate r i).val=0 := by
      cases r with
      | zero => omega
      | succ r =>
        have hi' : i=Fin.last r := Fin.ext (by simpa using hi)
        rw [hi']
        simp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hB
    rcases hB with rfl|rfl
    · simp only [List.sum_cons,List.sum_nil,add_zero]
      rw [he]
      exact lower_wrap_bound i.val
    · have hd:=lowerDelta_le r
      simp only [List.sum_cons,List.sum_nil,add_zero]
      linarith
  · rename_i hbad
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hB
    subst B
    simpa [add_assoc] using lower_triple_bound hr s.1 s.2 hbad

lemma triples_perm {α : Type*} (L : List α) (f g h : α→ℝ) :
    (L.flatMap (fun s=>[f s,g s,h s])).Perm (L.map f++L.map g++L.map h) := by
  have h1:=List.map_append_flatMap_perm L f (fun s=>[g s,h s])
  have h2:=List.map_append_flatMap_perm L g (fun s=>[h s])
  simpa only [← List.map_eq_flatMap, List.append_assoc] using
    h1.symm.trans (h2.symm.append_left (L.map f))

lemma lowerOpt_perm (r : ℕ) : (lowerOptPacking r).flatten.Perm (lowerList r) := by
  have hp := (lowerPartner_perm r).map (fun s=>bValue s.1 s.2)
  simp only [List.map_map] at hp
  have ht:=triples_perm (lowerSlots r) (fun s=>aValue s.1 s.2)
    (fun s=>bValue (lowerPartner r s).1 (lowerPartner r s).2) (fun _=>1/2+lowerDelta r)
  have he : (lowerOptPacking r).flatten =
      (lowerSlots r).flatMap (fun s=>[aValue s.1 s.2,
        bValue (lowerPartner r s).1 (lowerPartner r s).2,1/2+lowerDelta r]) := by
    simp only [lowerOptPacking,lower_flatten_flatMap,lowerGoodGroups_flatten]
  rw [he]
  apply ht.trans
  have hh:= (List.Perm.refl ((lowerSlots r).map (fun s=>aValue s.1 s.2))).append hp
  have hh:=hh.append (List.Perm.refl ((lowerSlots r).map (fun _=>1/2+lowerDelta r)))
  simpa [lowerSlots_a,lowerSlots_b,List.map_const',lowerSlots_length,lowerList,
    lowerPacking,List.flatten_append,Function.comp_def] using hh

lemma lowerOpt_length {r : ℕ} (hr : 0<r) : (lowerOptPacking r).length=10*r+1 := by
  classical
  let bad : Fin r × Fin 10 := (⟨r-1,by omega⟩,1)
  have hb (s : Fin r × Fin 10) : (s.1.val=r-1 ∧ s.2=1) ↔ s=bad := by
    constructor
    · rintro ⟨h1,h2⟩
      exact Prod.ext (Fin.ext h1) h2
    · intro h
      subst s
      exact ⟨rfl,rfl⟩
  have hg (L : List (Fin r × Fin 10)) :
      (L.flatMap (lowerGoodGroups r)).length=L.length+L.count bad := by
    induction L with
    | nil => simp
    | cons a L ih =>
      simp only [List.flatMap_cons,List.length_append,ih,List.length_cons,List.count_cons]
      unfold lowerGoodGroups
      by_cases h:a=bad <;> simp [hb,h,beq_iff_eq] <;> omega
  rw [lowerOptPacking,hg,lowerSlots_length,(lowerSlots_nodup r).count]
  simp [mem_lowerSlots]

lemma lower_optimum {r : ℕ} (hr : 0<r) : optBins (lowerList r)=10*r+1 := by
  have hu := optimum_le (feasible_of_perm_flatten (lowerOpt_perm r) (lowerOpt_capacity hr))
  rw [lowerOpt_length hr] at hu
  have hv:=volume_le_optimum (lowerList r) (lowerList_valid r)
  have hl:=lowerList_mass_gt hr
  have hn : 10*r<optBins (lowerList r) := by exact_mod_cast (lt_of_lt_of_le hl hv)
  omega

end BinPacking.FirstFit.Proof
-- End LowerOptimal

-- Begin LowerPadding

namespace BinPacking.FirstFit.Proof

lemma fold_ones (choose : List (List ℝ)→ℝ→ℕ) (hc : ChoiceRule choose)
    (B : List (List ℝ)) (hB : ∀C∈B,0<C.sum) (s : ℕ) :
    (List.replicate s (1:ℝ)).foldl (fun bins a=>placeAt bins (choose bins a) a) B =
      B++List.replicate s [1] := by
  induction s generalizing B with
  | zero => simp
  | succ s ih =>
    rw [List.replicate_succ,List.foldl_cons]
    have hn : choose B 1=B.length := choice_new_of_no_fit choose hc B 1 (by
      intro C hC
      linarith [hB C hC])
    rw [hn]
    have hp : placeAt B B.length 1=B++[[1]] := by simp [placeAt]
    rw [hp,ih]
    · simp [List.replicate_succ,List.append_assoc]
    · intro C hC
      rcases List.mem_append.mp hC with hC|hC
      · exact hB C hC
      · simp only [List.mem_singleton] at hC
        subst C
        norm_num

lemma lowerPacking_pos (r : ℕ) : ∀B∈lowerPacking r,0<B.sum := by
  intro B hB
  exact List.sum_pos B (fun a ha=>(lowerPacking_items r B hB a ha).1) (lowerPacking_nonempty r B hB)

noncomputable def paddedLower (r s : ℕ) : List ℝ := lowerList r++List.replicate s 1

lemma paddedLower_valid (r s : ℕ) : IsList (paddedLower r s) := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact lowerList_valid r x hx
  · have hx1 : x=1 := (List.mem_replicate.mp hx).2
    subst x
    norm_num

lemma paddedLower_counts (r s : ℕ) :
    FF (paddedLower r s)=17*r+s ∧ BF (paddedLower r s)=17*r+s := by
  have h (choose) (hc:ChoiceRule choose) : (run choose (paddedLower r s)).length=17*r+s := by
    rw [paddedLower,run_append,run_lowerList choose hc,
      fold_ones choose hc _ (lowerPacking_pos r)]
    simp [lowerPacking_length]
  exact ⟨h ffChoice ff_choice_rule,h bfChoice bf_choice_rule⟩

lemma paddedLower_feasible {r : ℕ} (hr : 0<r) (s : ℕ) :
    FeasiblePacking (paddedLower r s) (10*r+1+s) := by
  have hp : ((lowerOptPacking r)++List.replicate s [1]).flatten.Perm (paddedLower r s) := by
    simpa [paddedLower] using (lowerOpt_perm r).append (List.Perm.refl (List.replicate s 1))
  have hf:=feasible_of_perm_flatten hp (by
    intro B hB
    rcases List.mem_append.mp hB with hB|hB
    · exact lowerOpt_capacity hr B hB
    · have he: B=[1] := (List.mem_replicate.mp hB).2
      subst B
      norm_num)
  simpa [lowerOpt_length hr] using hf

lemma paddedLower_optimum {r : ℕ} (hr : 0<r) (s : ℕ) :
    optBins (paddedLower r s)=10*r+1+s := by
  have hu:=optimum_le (paddedLower_feasible hr s)
  have hv:=volume_le_optimum (paddedLower r s) (paddedLower_valid r s)
  have hl:=lowerList_mass_gt hr
  have hm : (10*r+s:ℝ)<(paddedLower r s).sum := by
    simp only [paddedLower,List.sum_append,List.sum_replicate,nsmul_eq_mul,mul_one]
    linarith
  have hn : 10*r+s<optBins (paddedLower r s) := by exact_mod_cast (lt_of_lt_of_le hm hv)
  omega

lemma ones_valid (k : ℕ) : IsList (List.replicate k (1:ℝ)) := by
  intro x hx
  have he : x=1 := (List.mem_replicate.mp hx).2
  subst x
  norm_num

lemma ones_optimum (k : ℕ) : optBins (List.replicate k (1:ℝ))=k := by
  have hu:=optimum_le_length _ (ones_valid k)
  have hl:=volume_le_optimum _ (ones_valid k)
  simp only [List.length_replicate] at hu
  simp only [List.sum_replicate,nsmul_eq_mul,mul_one] at hl
  exact le_antisymm hu (by exact_mod_cast hl)

lemma ones_counts (k : ℕ) : FF (List.replicate k (1:ℝ))=k ∧ BF (List.replicate k (1:ℝ))=k := by
  have h (choose) (hc:ChoiceRule choose) : (run choose (List.replicate k (1:ℝ))).length=k := by
    have hh:=fold_ones choose hc [] (by simp) k
    simpa [run] using congrArg List.length hh
  exact ⟨h ffChoice ff_choice_rule,h bfChoice bf_choice_rule⟩

theorem exists_lower (k : ℕ) (hk : 1≤k) :
    ∃L,IsList L ∧ optBins L=k ∧ 17/10*(k:ℝ)-8≤FF L ∧ 17/10*(k:ℝ)-8≤BF L := by
  by_cases hk11 : 11≤k
  · let r:ℕ := (k-1)/10
    let s:ℕ := (k-1)%10
    have hr:0<r := by dsimp [r]; omega
    have hs:s≤9 := by dsimp [s]; omega
    have he:k=10*r+1+s := by dsimp [r,s]; omega
    refine ⟨paddedLower r s,paddedLower_valid r s,?_,?_,?_⟩
    · rw [paddedLower_optimum hr,he]
    all_goals
      simp only [(paddedLower_counts r s).1,(paddedLower_counts r s).2]
      rw [he]
      have hs':(s:ℝ)≤9 := by exact_mod_cast hs
      push_cast
      linarith
  · refine ⟨List.replicate k 1,ones_valid k,ones_optimum k,?_,?_⟩
    all_goals
      have hk':(k:ℝ)≤10 := by exact_mod_cast (show k≤10 by omega)
      simp only [(ones_counts k).1,(ones_counts k).2]
      linarith

end BinPacking.FirstFit.Proof
-- End LowerPadding

-- Begin RootAssembly

namespace BinPacking.FirstFit

theorem ratio_limit_eq :
    Filter.Tendsto ratioFF Filter.atTop (nhds ((17 : ENNReal) / 10)) ∧
    Filter.Tendsto ratioBF Filter.atTop (nhds ((17 : ENNReal) / 10)) := by
  constructor
  · apply Proof.ratio_tendsto_of_bounds FF Proof.ff_upper
    intro k hk
    obtain ⟨L,hL,he,hf,_⟩ := Proof.exists_lower k hk
    exact ⟨L,hL,he,hf⟩
  · apply Proof.ratio_tendsto_of_bounds BF Proof.bf_upper
    intro k hk
    obtain ⟨L,hL,he,_,hb⟩ := Proof.exists_lower k hk
    exact ⟨L,hL,he,hb⟩

end BinPacking.FirstFit
-- End RootAssembly

-- Begin Solution

theorem solution :
    Filter.Tendsto BinPacking.FirstFit.ratioFF Filter.atTop (nhds ((17 : ENNReal) / 10)) ∧
    Filter.Tendsto BinPacking.FirstFit.ratioBF Filter.atTop (nhds ((17 : ENNReal) / 10)) :=
  BinPacking.FirstFit.ratio_limit_eq
-- End Solution
