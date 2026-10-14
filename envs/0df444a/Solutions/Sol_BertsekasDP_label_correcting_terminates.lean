-- Prove2me | solution 1 for BertsekasDP.label_correcting_terminates
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T06:50:25.294203+00:00
-- url     : https://prove2.me/submissions/8d381956-74f2-41b3-afac-96839b82f0ae

import Definitions.Def_BertsekasSPGraph
import Definitions.Def_BertsekasLCState
import Mathlib.Data.Fintype.List
import Mathlib.Order.OrderIsoNat

/- Walk append and length lemmas adapted from wamlart's accepted invariant proof,
   submission 9f3cf73d-d36f-4d55-ae52-045bb482c689 on Prove2Me. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DPTerminationProof
variable {V : Type} [Fintype V] [DecidableEq V] (G : BertsekasSPGraph V)

lemma walk_append {a i j : V} {l : List V}
    (h : BertsekasIsWalkFrom G a i l) (hij : (i,j) ∈ G.arcs) :
    BertsekasIsWalkFrom G a j (l ++ [j]) := by
  rcases h with ⟨hne,hchain,hhead,hlast⟩
  refine ⟨by simp, hchain.append (by simp) ?_, ?_, by simp⟩
  · intro x hx y hy
    simp only [hlast, Option.mem_some_iff] at hx
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst x
    subst y
    exact hij
  · simp [List.head?_append, hhead]

lemma length_cons (a b : V) (l : List V) :
    BertsekasWalkLength G (a :: b :: l) = G.length a b + BertsekasWalkLength G (b :: l) := by
  simp [BertsekasWalkLength]

lemma length_append {i j : V} {l : List V} (hne : l ≠ []) (hlast : l.getLast? = some i) :
    BertsekasWalkLength G (l ++ [j]) = BertsekasWalkLength G l + G.length i j := by
  induction l with
  | nil => simp at hne
  | cons a l ih =>
    cases l with
    | nil =>
      have hai : a = i := by simpa using hlast
      subst a
      simp [BertsekasWalkLength]
    | cons b l =>
      have ht := ih (by simp) (by simpa using hlast)
      simp only [List.cons_append] at ht
      simp only [List.cons_append, length_cons] at ⊢
      rw [ht]
      ring

lemma length_split (pre : List V) (v : V) (post : List V) :
    BertsekasWalkLength G (pre ++ v :: post) =
      BertsekasWalkLength G (pre ++ [v]) + BertsekasWalkLength G (v :: post) := by
  induction pre with
  | nil => simp [BertsekasWalkLength]
  | cons a pre ih =>
    cases pre with
    | nil => simp [BertsekasWalkLength]
    | cons b pre =>
      simp only [List.cons_append,length_cons] at ih ⊢
      rw [ih]
      ring

/-- Each occurrence has a prefix whose cost bounds its current label. -/
def supported (d : V → EReal) (l : List V) : Prop :=
  ∀ v ∈ l, ∃ pre post : List V,
    l = pre ++ v :: post ∧ d v ≤ (BertsekasWalkLength G (pre ++ [v]) : EReal)

def good (σ : BertsekasLCState V) : Prop :=
  ∀ j : V, σ.label j = ⊤ ∨ ∃ l : List V,
    BertsekasIsWalkFrom G G.s j l ∧ l.Nodup ∧
      σ.label j = (BertsekasWalkLength G l : EReal) ∧ supported G σ.label l

lemma supported_mono {d e : V → EReal} {l : List V}
    (h : supported G d l) (he : ∀ v, e v ≤ d v) : supported G e l := by
  intro v hv
  obtain ⟨pre,post,hl,hv⟩ := h v hv
  exact ⟨pre,post,hl,(he v).trans hv⟩

lemma initial_good : good G (BertsekasLCInit G) := by
  intro j
  by_cases hj : j = G.s
  · subst j
    refine Or.inr ⟨[G.s],by simp [BertsekasIsWalkFrom],by simp,?_,?_⟩
    · simp [BertsekasLCInit,BertsekasWalkLength]
    · intro v hv
      have hv' : v = G.s := List.mem_singleton.mp hv
      subst v
      exact ⟨[],[],rfl,by simp [BertsekasLCInit,BertsekasWalkLength]⟩
  · exact Or.inl (by simp [BertsekasLCInit,hj])

lemma child_label_le (i j : V) (σ : BertsekasLCState V) (v : V) :
    (BertsekasLCProcessChild G i σ j).label v ≤ σ.label v := by
  classical
  unfold BertsekasLCProcessChild
  split
  · rename_i hc
    by_cases hv : v = j
    · subst v
      simpa using (hc.2.trans_le (min_le_left _ _)).le
    · simp [Function.update_of_ne hv]
  · exact le_rfl

lemma child_good
    (hcyc : ∀ v l, BertsekasIsWalkFrom G v v l → 0 ≤ BertsekasWalkLength G l)
    (i j : V) (σ : BertsekasLCState V) (hσ : good G σ) :
    good G (BertsekasLCProcessChild G i σ j) := by
  classical
  let τ := BertsekasLCProcessChild G i σ j
  have hm (v : V) : τ.label v ≤ σ.label v := child_label_le G i j σ v
  by_cases hc : (i,j) ∈ G.arcs ∧
      σ.label i + (G.length i j : EReal) < min (σ.label j) σ.upper
  · have hfinite : σ.label i ≠ ⊤ := by
      intro ht
      have hh := hc.2
      simp [ht] at hh
    obtain ⟨l,hl,hnd,he,hs⟩ := (hσ i).resolve_left hfinite
    have hwalk := walk_append G hl hc.1
    have hlen := length_append G hl.1 hl.2.2.2 (j := j)
    have hcand : σ.label i + (G.length i j : EReal) =
        (BertsekasWalkLength G (l ++ [j]) : EReal) := by
      rw [he,hlen,EReal.coe_add]
    have hjnot : j ∉ l := by
      intro hj
      obtain ⟨pre,post,hdecomp,hprefix⟩ := hs j hj
      have hcycle : BertsekasIsWalkFrom G j j (j :: (post ++ [j])) := by
        refine ⟨by simp,?_,by simp,?_⟩
        · apply hwalk.2.1.suffix
          refine ⟨pre,?_⟩
          simp [hdecomp,List.append_assoc]
        · change ((j :: post) ++ [j]).getLast? = some j
          exact List.getLast?_concat
      have hnonneg := hcyc j _ hcycle
      have hsplit : BertsekasWalkLength G (l ++ [j]) =
          BertsekasWalkLength G (pre ++ [j]) +
            BertsekasWalkLength G (j :: (post ++ [j])) := by
        simpa [hdecomp,List.append_assoc] using length_split G pre j (post ++ [j])
      have hcost : BertsekasWalkLength G (pre ++ [j]) ≤ BertsekasWalkLength G (l ++ [j]) := by
        rw [hsplit]
        linarith
      have hle := hprefix.trans (EReal.coe_le_coe_iff.mpr hcost)
      have hlt := hc.2.trans_le (min_le_left _ _)
      rw [hcand] at hlt
      exact (not_lt_of_ge hle) hlt
    have htj : τ.label j = (BertsekasWalkLength G (l ++ [j]) : EReal) := by
      simpa [τ,BertsekasLCProcessChild,hc] using hcand
    intro v
    by_cases hv : v = j
    · subst v
      refine Or.inr ⟨l ++ [j],hwalk,by simpa using hnd.concat hjnot,htj,?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨pre,post,hdecomp,hprefix⟩ := hs v hv
        refine ⟨pre,post ++ [j],by simp [hdecomp,List.append_assoc],(hm v).trans hprefix⟩
      · have hvj : v = j := List.mem_singleton.mp hv
        subst v
        exact ⟨l,[],by simp,htj.le⟩
    · have htv : τ.label v = σ.label v := by simp [τ,BertsekasLCProcessChild,hc,hv]
      rcases hσ v with htop | ⟨lv,hlv,hndv,hev,hsv⟩
      · exact Or.inl (htv.trans htop)
      · exact Or.inr ⟨lv,hlv,hndv,htv.trans hev,supported_mono G hsv hm⟩
  · simpa only [BertsekasLCProcessChild,if_neg hc] using hσ

lemma fold_good
    (hcyc : ∀ v l, BertsekasIsWalkFrom G v v l → 0 ≤ BertsekasWalkLength G l)
    (i : V) (js : List V) (σ : BertsekasLCState V) (hσ : good G σ) :
    good G (js.foldl (BertsekasLCProcessChild G i) σ) := by
  induction js generalizing σ with
  | nil => exact hσ
  | cons j js ih => exact ih _ (child_good G hcyc i j σ hσ)

lemma step_good
    (hcyc : ∀ v l, BertsekasIsWalkFrom G v v l → 0 ≤ BertsekasWalkLength G l)
    {σ τ : BertsekasLCState V} (hσ : good G σ) (hstep : BertsekasLCStep G σ τ) : good G τ := by
  obtain ⟨i,hi,js,hperm,rfl⟩ := hstep
  exact fold_good G hcyc i js _ hσ

lemma reachable_good
    (hcyc : ∀ v l, BertsekasIsWalkFrom G v v l → 0 ≤ BertsekasWalkLength G l)
    (σ : BertsekasLCState V)
    (hreach : Relation.ReflTransGen (BertsekasLCStep G) (BertsekasLCInit G) σ) : good G σ := by
  induction hreach with
  | refl => exact initial_good G
  | tail hreach hstep ih => exact step_good G hcyc ih hstep


lemma fold_label_le (i : V) (js : List V) (σ : BertsekasLCState V) (v : V) :
    (js.foldl (BertsekasLCProcessChild G i) σ).label v ≤ σ.label v := by
  induction js generalizing σ with
  | nil => exact le_rfl
  | cons j js ih => exact (ih _).trans (child_label_le G i j σ v)

lemma step_label_le {σ τ : BertsekasLCState V} (hstep : BertsekasLCStep G σ τ) (v : V) :
    τ.label v ≤ σ.label v := by
  obtain ⟨i,hi,js,hperm,rfl⟩ := hstep
  exact fold_label_le G i js _ v

lemma child_eq_of_label_eq (i j : V) (σ : BertsekasLCState V)
    (he : (BertsekasLCProcessChild G i σ j).label = σ.label) :
    BertsekasLCProcessChild G i σ j = σ := by
  classical
  unfold BertsekasLCProcessChild at he ⊢
  split
  · rename_i hc
    have h := congrFun he j
    simp only [if_pos hc,Function.update_self] at h
    have hlt := hc.2.trans_le (min_le_left _ _)
    rw [h] at hlt
    exact False.elim (lt_irrefl _ hlt)
  · rfl

lemma fold_eq_of_label_eq (i : V) (js : List V) (σ : BertsekasLCState V)
    (he : (js.foldl (BertsekasLCProcessChild G i) σ).label = σ.label) :
    js.foldl (BertsekasLCProcessChild G i) σ = σ := by
  induction js generalizing σ with
  | nil => rfl
  | cons j js ih =>
    let τ := BertsekasLCProcessChild G i σ j
    have hchild : τ.label = σ.label := by
      funext v
      apply le_antisymm (child_label_le G i j σ v)
      have hle := fold_label_le G i js τ v
      change (js.foldl (BertsekasLCProcessChild G i) τ).label = σ.label at he
      rw [he] at hle
      exact hle
    have hτ : τ = σ := child_eq_of_label_eq G i j σ hchild
    change js.foldl (BertsekasLCProcessChild G i) τ = σ
    change (js.foldl (BertsekasLCProcessChild G i) τ).label = σ.label at he
    rw [hτ] at he ⊢
    exact ih σ he

lemma step_card_lt_of_label_eq {σ τ : BertsekasLCState V}
    (hstep : BertsekasLCStep G σ τ) (he : τ.label = σ.label) :
    τ.openList.card < σ.openList.card := by
  obtain ⟨i,hi,js,hperm,rfl⟩ := hstep
  have hf := fold_eq_of_label_eq G i js {σ with openList := σ.openList.erase i} he
  rw [hf]
  exact Finset.card_erase_lt_of_mem hi

private def values : Finset EReal :=
  insert ⊤ (Finset.univ.image fun l : {l : List V // l.Nodup} =>
    (BertsekasWalkLength G l.val : EReal))

lemma label_mem_values {σ : BertsekasLCState V} (hσ : good G σ) (v : V) :
    σ.label v ∈ values G := by
  classical
  rcases hσ v with htop | ⟨l,hl,hnd,he,hs⟩
  · simp [values,htop]
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨⟨l,hnd⟩,Finset.mem_univ _,he.symm⟩

end DPTerminationProof

open DPTerminationProof

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hcyc : ∀ v l, BertsekasIsWalkFrom G v v l → 0 ≤ BertsekasWalkLength G l) :
    ¬ ∃ seq : ℕ → BertsekasLCState V,
        seq 0 = BertsekasLCInit G ∧
        ∀ k, BertsekasLCStep G (seq k) (seq (k + 1)) := by
  classical
  rintro ⟨seq,hinit,hstep⟩
  have hreach (n : ℕ) :
      Relation.ReflTransGen (BertsekasLCStep G) (BertsekasLCInit G) (seq n) := by
    induction n with
    | zero => simpa only [hinit] using (Relation.ReflTransGen.refl (r := BertsekasLCStep G) (a := BertsekasLCInit G))
    | succ n ih => exact ih.tail (hstep n)
  let F (n : ℕ) (v : V) : ↥(values G) :=
    ⟨(seq n).label v,label_mem_values G (reachable_good G hcyc (seq n) (hreach n)) v⟩
  have hanti : Antitone F := by
    apply antitone_nat_of_succ_le
    intro n v
    exact step_label_le G (hstep n) v
  have hfin : (Set.range F).Finite := Set.toFinite _
  obtain ⟨a,ha,hmin⟩ := hfin.exists_minimal (Set.range_nonempty F)
  obtain ⟨n,rfl⟩ := ha
  have hstable (m : ℕ) (hnm : n ≤ m) : (seq m).label = (seq n).label := by
    have hFm : F m = F n := le_antisymm (hanti hnm) (hmin (Set.mem_range_self m) (hanti hnm))
    funext v
    exact congrArg Subtype.val (congrFun hFm v)
  have hcard (r : ℕ) : (seq (n+(r+1))).openList.card < (seq (n+r)).openList.card := by
    apply step_card_lt_of_label_eq G (by simpa only [Nat.add_assoc] using hstep (n+r))
    exact (hstable (n+(r+1)) (by omega)).trans (hstable (n+r) (by omega)).symm
  have hbound (r : ℕ) : (seq (n+r)).openList.card + r ≤ (seq n).openList.card := by
    induction r with
    | zero => simp
    | succ r ih => have h := hcard r; omega
  have hh := hbound ((seq n).openList.card+1)
  omega
