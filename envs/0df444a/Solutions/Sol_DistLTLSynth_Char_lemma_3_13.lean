-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T12:45:59.074171+00:00
-- url     : https://prove2.me/submissions/04d0288c-2ab1-4a36-b01a-08acbf34a88a

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine
import Definitions.Def_DistLTLSynth_Char_SymbolicArena

set_option autoImplicit false

namespace DistLTLSynth.Char.Lemma313Aux

open DistLTLSynth.Char

lemma primrec₂_natPair : Primrec₂ Nat.pair := Primrec.encode

lemma iterNat_succ {α : Type} (g : α → α) (m : ℕ) (x : α) :
    iterNat g (m + 1) x = g (iterNat g m x) := by
  simp [iterNat, List.range_succ]

lemma list_sections_primrec {α : Type} [Primcodable α] :
    Primrec (List.sections (α := α)) := by
  have hf : Primrec (fun xs : List (List α) => xs.foldr
      (fun choices tails => tails.flatMap (fun tail => choices.map (fun a => a :: tail))) [[]]) :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
        (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂
  exact hf.of_eq (fun xs => by induction xs <;> simp_all [List.sections])

lemma wordsOf_primrec {α : Type} [Primcodable α] : Primrec₂ (wordsOf (α := α)) :=
  list_sections_primrec.comp
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) (Primrec.fst.comp Primrec.fst).to₂)

lemma mem_dedupList {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ dedupList xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [dedupList]
  | cons x xs ih =>
    change a ∈ (if x ∈ dedupList xs then dedupList xs else x :: dedupList xs) ↔ a ∈ x :: xs
    split_ifs with h
    · have hx := (ih x).mp h
      simp only [ih, List.mem_cons]
      exact ⟨Or.inr, fun hc => hc.elim (fun he => he ▸ hx) id⟩
    · simp only [List.mem_cons, ih]

lemma nodup_dedupList {α : Type} [DecidableEq α] (xs : List α) : (dedupList xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    change (if x ∈ dedupList xs then dedupList xs else x :: dedupList xs).Nodup
    split_ifs with h
    · exact ih
    · exact List.nodup_cons.mpr ⟨h, ih⟩

lemma dedupList_primrec {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupList (α := α)) := by
  have hm : PrimrecRel (fun (ys : List α) (x : α) => x ∈ ys) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (hm.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂

lemma view1_append_singleton {X1 X2 : Type} (l : List (Signal X1 X2)) (s : Signal X1 X2) :
    view1 (l ++ [s]) = (viewStep (view1 l, view2 l) s).1 := by
  simp [view1, view2, views]

lemma view2_append_singleton {X1 X2 : Type} (l : List (Signal X1 X2)) (s : Signal X1 X2) :
    view2 (l ++ [s]) = (viewStep (view1 l, view2 l) s).2 := by
  simp [view1, view2, views]

lemma vdepth_views {X1 X2 : Type} (l : List (Signal X1 X2)) :
    vdepth (view1 l) = l.length ∧ vdepth (view2 l) = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [view1, view2, views, vdepth]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    rw [view1_append_singleton, view2_append_singleton]
    cases g <;> simp [viewStep, vdepth, ih.1, ih.2]

lemma viewStep1_eq_ite {X1 X2 : Type} [DecidableEq CommGraph]
    (uv : View X1 X2 × View X1 X2) (x1 : X1) (x2 : X2) (g : CommGraph) :
    (viewStep uv (x1, x2, g)).1 =
      if g = .oneToTwo then .N1 x1 uv.1 else .C1 x1 uv.1 x2 uv.2 := by
  cases g <;> simp [viewStep]

lemma viewStep2_eq_ite {X1 X2 : Type} [DecidableEq CommGraph]
    (uv : View X1 X2 × View X1 X2) (x1 : X1) (x2 : X2) (g : CommGraph) :
    (viewStep uv (x1, x2, g)).2 =
      if g = .twoToOne then .N2 x2 uv.2 else .C2 x2 uv.2 x1 uv.1 := by
  cases g <;> simp [viewStep]

lemma bounded_seq_min_inf_often (K : ℕ) (c : ℕ → ℕ) (hb : ∀ n, c n ≤ K) :
    ∃ p ≤ K, (∃ᶠ n in Filter.atTop, c n = p) ∧ (∀ᶠ n in Filter.atTop, p ≤ c n) := by
  classical
  have hex : ∃ p : ℕ, p ≤ K ∧ ∃ᶠ n in Filter.atTop, c n = p := by
    by_contra hall
    have hnone : ∀ p ≤ K, ∃ N : ℕ, ∀ n ≥ N, c n ≠ p := by
      intro p hp
      have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = p := fun hf => hall ⟨p, hp, hf⟩
      rw [Filter.frequently_atTop] at hnf
      by_contra hnoN
      apply hnf
      intro N
      by_contra hno_n
      exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
    let boundOf : ℕ → ℕ := fun p => if hp : p ≤ K then (hnone p hp).choose else 0
    let M := (Finset.range (K + 1)).sup boundOf
    have hcM : c M ≤ K := hb M
    have hleM : boundOf (c M) ≤ M :=
      Finset.le_sup (f := boundOf) (Finset.mem_range.mpr (by omega))
    have hspec : ∀ n ≥ boundOf (c M), c n ≠ c M := by
      dsimp only [boundOf]; rw [dif_pos hcM]; exact (hnone (c M) hcM).choose_spec
    exact hspec M hleM rfl
  let p := Nat.find hex
  have hp_spec : p ≤ K ∧ ∃ᶠ n in Filter.atTop, c n = p := Nat.find_spec hex
  have hp_min : ∀ q < p, ¬ (q ≤ K ∧ ∃ᶠ n in Filter.atTop, c n = q) :=
    fun q hq => Nat.find_min hex hq
  have hno_lt : ∀ q < p, ∃ N : ℕ, ∀ n ≥ N, c n ≠ q := by
    intro q hq
    have hqK : q ≤ K := le_trans (le_of_lt hq) hp_spec.1
    have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = q := fun hf => hp_min q hq ⟨hqK, hf⟩
    rw [Filter.frequently_atTop] at hnf
    by_contra hnoN
    apply hnf
    intro N
    by_contra hno_n
    exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
  let boundLt : ℕ → ℕ := fun q => if hq : q < p then (hno_lt q hq).choose else 0
  let N0 := (Finset.range p).sup boundLt
  refine ⟨p, hp_spec.1, hp_spec.2, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N0, fun n hn => ?_⟩
  by_contra hlt
  have hcp : c n < p := by omega
  have hleN : boundLt (c n) ≤ N0 := Finset.le_sup (f := boundLt) (Finset.mem_range.mpr hcp)
  have hspec : ∀ m ≥ boundLt (c n), c m ≠ c n := by
    dsimp only [boundLt]; rw [dif_pos hcp]; exact (hno_lt (c n) hcp).choose_spec
  exact hspec n (le_trans hleN hn) rfl

lemma getD_eq_getElem {α : Type} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

lemma getD_of_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma not_parityCond_and_oddParityCond (c : ℕ → ℕ) :
    ¬ (ParityCond c ∧ OddParityCond c) := by
  rintro ⟨⟨p, hp_even, hp_freq, hp_ev⟩, ⟨q, hq_odd, hq_freq, hq_ev⟩⟩
  obtain ⟨n1, hn1_eq, hn1_le⟩ := (hq_freq.and_eventually hp_ev).exists
  obtain ⟨n2, hn2_eq, hn2_le⟩ := (hp_freq.and_eventually hq_ev).exists
  have hpq : p = q := by omega
  subst hpq
  rcases hp_even with ⟨k, rfl⟩
  rcases hq_odd with ⟨l, hl⟩
  omega

lemma parityCond_or_oddParityCond_of_bdd (c : ℕ → ℕ) (K : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ K) :
    ParityCond c ∨ OddParityCond c := by
  obtain ⟨p, _, hfreq, hev⟩ := bounded_seq_min_inf_often K c hbdd
  rcases Nat.even_or_odd p with heven | hodd
  · exact Or.inl ⟨p, heven, hfreq, hev⟩
  · exact Or.inr ⟨p, hodd, hfreq, hev⟩

lemma oddParityCond_iff_not_parityCond_of_bdd (c : ℕ → ℕ) (K : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ K) :
    OddParityCond c ↔ ¬ ParityCond c := by
  constructor
  · intro ho hp
    exact not_parityCond_and_oddParityCond c ⟨hp, ho⟩
  · intro hnp
    rcases parityCond_or_oddParityCond_of_bdd c K hbdd with hp | ho
    · exact False.elim (hnp hp)
    · exact ho

lemma exists_inf_state_of_frequently {Q : Type} [Fintype Q] (ρ : ℕ → Q) (P : Q → Prop)
    (hfreq : ∃ᶠ n in Filter.atTop, P (ρ n)) :
    ∃ q : Q, P q ∧ ∃ᶠ n in Filter.atTop, ρ n = q := by
  by_contra hno
  have hall : ∀ q : Q, ∀ᶠ n in Filter.atTop, ¬ (P q ∧ ρ n = q) := by
    intro q
    by_cases hq : P q
    · have hnf : ¬ ∃ᶠ n in Filter.atTop, ρ n = q := fun hf => hno ⟨q, hq, hf⟩
      rw [Filter.not_frequently] at hnf
      exact hnf.mono fun n hn h => hn h.2
    · exact Filter.Eventually.of_forall fun _ h => hq h.1
  have hev : ∀ᶠ n in Filter.atTop, ¬ P (ρ n) :=
    (Filter.eventually_all.mpr hall).mono fun n hn hp => hn (ρ n) ⟨hp, rfl⟩
  exact (Filter.not_frequently.mpr hev) hfreq

lemma ListNBWAccepts_iff_frequently (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) :
    ListNBWAccepts αSize B w ↔
      ∃ ρ : ℕ → Fin (B.1 + 1),
        (ρ 0).val ∈ B.2.1 ∧
        (∀ n, (ρ (n + 1)).val ∈ B.2.2.1.getD ((αSize + 1) * (ρ n).val + (w n).val) []) ∧
        ∃ᶠ n in Filter.atTop, (ρ n).val ∈ B.2.2.2 := by
  constructor
  · rintro ⟨ρ, h0, hstep, q, hq, hfreq⟩
    exact ⟨ρ, h0, hstep, hfreq.mono fun n hn => hn ▸ hq⟩
  · rintro ⟨ρ, h0, hstep, hfreq⟩
    obtain ⟨q, hq, hqfreq⟩ := exists_inf_state_of_frequently ρ (fun q => q.val ∈ B.2.2.2) hfreq
    exact ⟨ρ, h0, hstep, q, hq, hqfreq⟩

lemma primrec₂_cMax : Primrec₂ cMax :=
  Primrec.ite Primrec.nat_le Primrec.snd Primrec.fst

lemma cMax_eq_max (a b : ℕ) : cMax a b = max a b := by
  unfold cMax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (Nat.le_of_not_le h)).symm

lemma primrec_maxList : Primrec maxList :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (primrec₂_cMax.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

lemma le_maxList_of_mem {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ maxList xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [maxList, List.foldr_cons, cMax_eq_max]
    rcases List.mem_cons.mp hx with rfl | htl
    · exact le_max_left _ _
    · exact le_trans (ih htl) (le_max_right _ _)

lemma getD_zero_le_maxList (xs : List ℕ) (i : ℕ) : xs.getD i 0 ≤ maxList xs := by
  by_cases hi : i < xs.length
  · rw [getD_eq_getElem xs 0 i hi]
    exact le_maxList_of_mem (List.getElem_mem hi)
  · rw [getD_of_ge xs 0 i (Nat.not_lt.mp hi)]
    exact Nat.zero_le _

lemma primrec_complementGenDPA : Primrec complementGenDPA := by
  have h1 : Primrec fun d : GenDPACode => d.1 := Primrec.fst
  have h2 : Primrec fun d : GenDPACode => d.2.1 := Primrec.fst.comp Primrec.snd
  have h3 : Primrec fun d : GenDPACode => (List.range (d.1 + 1)).map fun i => d.2.2.getD i 0 + 1 :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp h1))
      (Primrec.succ.comp ((Primrec.list_getD 0).comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂
  exact h1.pair (h2.pair h3)

lemma complementGenDPA_accepts_iff (αSize : ℕ) (d : GenDPACode) (w : ℕ → Fin (αSize + 1)) :
    (toGenDPA αSize (complementGenDPA d)).Accepts w ↔ ¬ (toGenDPA αSize d).Accepts w := by
  let M := toGenDPA αSize d
  let Mc := toGenDPA αSize (complementGenDPA d)
  have hrun : ∀ t, Mc.run w t = M.run w t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change Mc.step (Mc.run w t) (w t) = M.step (M.run w t) (w t)
      rw [ih]
      rfl
  have hprio : ∀ s : Fin (d.1 + 1), Mc.prio s = M.prio s + 1 := by
    intro s
    change ((List.range (d.1 + 1)).map fun i => d.2.2.getD i 0 + 1).getD s.val 0 = d.2.2.getD s.val 0 + 1
    rw [getD_eq_getElem _ 0 s.val (by simp [s.isLt])]
    simp
  have hbdd : ∀ t, M.prio (M.run w t) ≤ maxList d.2.2 :=
    fun t => getD_zero_le_maxList d.2.2 (M.run w t).val
  change ParityCond (fun t => Mc.prio (Mc.run w t)) ↔ ¬ ParityCond (fun t => M.prio (M.run w t))
  rw [← oddParityCond_iff_not_parityCond_of_bdd _ (maxList d.2.2) hbdd]
  have hfn : (fun t => Mc.prio (Mc.run w t)) = (fun t => M.prio (M.run w t) + 1) := by
    funext t; rw [hrun t, hprio]
  rw [hfn]
  constructor
  · rintro ⟨p, heven, hfreq, hev⟩
    obtain ⟨t0, ht0⟩ := hfreq.exists
    dsimp only at ht0
    have hp_pos : 1 ≤ p := by omega
    refine ⟨p - 1, ?_, ?_, ?_⟩
    · rcases heven with ⟨k, rfl⟩
      have hk_pos : 1 ≤ k := by omega
      exact ⟨k - 1, by omega⟩
    · exact hfreq.mono fun t ht => by dsimp only at ht ⊢; omega
    · exact hev.mono fun t ht => by dsimp only at ht ⊢; omega
  · rintro ⟨q, ⟨k, rfl⟩, hfreq, hev⟩
    exact ⟨2 * k + 2, ⟨k + 1, by ring⟩,
      hfreq.mono (fun t ht => by dsimp only at ht ⊢; omega),
      hev.mono (fun t ht => by dsimp only at ht ⊢; omega)⟩

lemma myPow_eq (b e : ℕ) : myPow b e = b ^ e := by
  unfold myPow
  induction e with
  | zero => simp
  | succ e ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, pow_succ]

lemma primrec₂_myPow : Primrec₂ myPow :=
  Primrec.list_foldl (Primrec.list_range.comp Primrec.snd) (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).to₂

lemma formula_ff_not_sat {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    ¬ (Formula.ff : Formula X1 X2 Y1 Y2).Sat e := by
  simp [Formula.ff, Formula.tt, Formula.Sat, em]

lemma instFormulaOf_sat (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ)
    (e : ℕ → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :
    (instFormulaOf I φ).Sat e ↔ φ.Sat (valExec e) := by
  induction φ generalizing e with
  | inp1 x =>
    dsimp only [instFormulaOf]
    by_cases hx : x < I.k1 + 1
    · rw [dif_pos hx]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg hx]
      simp only [formula_ff_not_sat, Formula.Sat, valExec, false_iff]
      intro heq; exact hx (heq ▸ (e 0).1.1.isLt)
  | inp2 x =>
    dsimp only [instFormulaOf]
    by_cases hx : x < I.k2 + 1
    · rw [dif_pos hx]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg hx]
      simp only [formula_ff_not_sat, Formula.Sat, valExec, false_iff]
      intro heq; exact hx (heq ▸ (e 0).1.2.1.isLt)
  | out1 y =>
    dsimp only [instFormulaOf]
    by_cases hy : y < I.m1 + 1
    · rw [dif_pos hy]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg hy]
      simp only [formula_ff_not_sat, Formula.Sat, valExec, false_iff]
      intro heq; exact hy (heq ▸ (e 0).2.1.isLt)
  | out2 y =>
    dsimp only [instFormulaOf]
    by_cases hy : y < I.m2 + 1
    · rw [dif_pos hy]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg hy]
      simp only [formula_ff_not_sat, Formula.Sat, valExec, false_iff]
      intro heq; exact hy (heq ▸ (e 0).2.2.isLt)
  | graph g => rfl
  | next φ ih => exact ih (shift e 1)
  | eventually φ ih => exact exists_congr fun r => ih (shift e r)
  | always φ ih => exact forall_congr' fun r => ih (shift e r)
  | untl φ ψ ih1 ih2 =>
    exact exists_congr fun r => and_congr (ih2 (shift e r))
      (forall_congr' fun r' => imp_congr_right fun _ => ih1 (shift e r'))
  | weakUntil ψ φ ih1 ih2 =>
    exact or_congr (forall_congr' fun r => ih1 (shift e r))
      (exists_congr fun r => and_congr (ih2 (shift e r))
        (forall_congr' fun r' => imp_congr_right fun _ => ih1 (shift e r')))
  | neg φ ih => exact not_congr (ih e)
  | or φ ψ ih1 ih2 => exact or_congr (ih1 e) (ih2 e)
  | and φ ψ ih1 ih2 => exact and_congr (ih1 e) (ih2 e)
  | imp φ ψ ih1 ih2 => exact imp_congr (ih1 e) (ih2 e)
  | iff φ ψ ih1 ih2 => exact iff_congr (ih1 e) (ih2 e)

lemma fRealizes_instFormulaOf_iff (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ)
    (A : Set (ℕ → CommGraph)) (f : Algorithm I.X1 I.X2 I.Y1 I.Y2) :
    FRealizes f A (instFormulaOf I φ) ↔ RealizesLang f A (I.Lang φ) := by
  unfold FRealizes RealizesLang Formula.Lang Instance.Lang
  exact forall_congr' fun h => imp_congr_right fun _ => instFormulaOf_sat I φ (exec f h)

lemma primrec_tokKind : Primrec tokKind := by
  have ht1 : Primrec fun t : Token => t.1 := Primrec.fst
  have ht21 : Primrec fun t : Token => t.2.1 := Primrec.fst.comp Primrec.snd
  have hp0 : PrimrecPred fun t : Token =>
      (t.1 = 0 ∧ (t.2.1 = 1 ∨ t.2.1 = 2)) ∨
      (t.1 = 1 ∧ (t.2.1 = 1 ∨ t.2.1 = 2)) ∨
      (t.1 = 2 ∧ t.2.1 ≤ 2) :=
    ((Primrec.eq.comp ht1 (Primrec.const 0)).and
      ((Primrec.eq.comp ht21 (Primrec.const 1)).or (Primrec.eq.comp ht21 (Primrec.const 2)))).or
    (((Primrec.eq.comp ht1 (Primrec.const 1)).and
      ((Primrec.eq.comp ht21 (Primrec.const 1)).or (Primrec.eq.comp ht21 (Primrec.const 2)))).or
      ((Primrec.eq.comp ht1 (Primrec.const 2)).and (Primrec.nat_le.comp ht21 (Primrec.const 2))))
  have hp1 : PrimrecPred fun t : Token => t.1 = 3 ∨ t.1 = 4 ∨ t.1 = 5 ∨ t.1 = 8 :=
    (Primrec.eq.comp ht1 (Primrec.const 3)).or
      ((Primrec.eq.comp ht1 (Primrec.const 4)).or
        ((Primrec.eq.comp ht1 (Primrec.const 5)).or (Primrec.eq.comp ht1 (Primrec.const 8))))
  have hp2 : PrimrecPred fun t : Token =>
      t.1 = 6 ∨ t.1 = 7 ∨ t.1 = 9 ∨ t.1 = 10 ∨ t.1 = 11 ∨ t.1 = 12 :=
    (Primrec.eq.comp ht1 (Primrec.const 6)).or
      ((Primrec.eq.comp ht1 (Primrec.const 7)).or
        ((Primrec.eq.comp ht1 (Primrec.const 9)).or
          ((Primrec.eq.comp ht1 (Primrec.const 10)).or
            ((Primrec.eq.comp ht1 (Primrec.const 11)).or (Primrec.eq.comp ht1 (Primrec.const 12))))))
  exact Primrec.ite hp0 (Primrec.const 0)
    (Primrec.ite hp1 (Primrec.const 1)
      (Primrec.ite hp2 (Primrec.const 2) (Primrec.const 3)))

lemma primrec_parseOk : Primrec parseOk := by
  have hcell : Primrec fun q : (List Token × List (Option ℕ)) × ℕ =>
      if q.2 < q.1.1.length then
        let k := tokKind (q.1.1.getD q.2 (99, 0, 0))
        if k = 0 then some (q.2 + 1)
        else if k = 1 then q.1.2.getD (q.2 + 1) none
        else if k = 2 then
          match q.1.2.getD (q.2 + 1) none with
          | some j => q.1.2.getD j none
          | none => none
        else none
      else none := by
    let Q := (List Token × List (Option ℕ)) × ℕ
    have hts : Primrec fun q : Q => q.1.1 := Primrec.fst.comp Primrec.fst
    have hprev : Primrec fun q : Q => q.1.2 := Primrec.snd.comp Primrec.fst
    have hi : Primrec fun q : Q => q.2 := Primrec.snd
    have hk : Primrec fun q : Q => tokKind (q.1.1.getD q.2 (99, 0, 0)) :=
      primrec_tokKind.comp ((Primrec.list_getD (99, 0, 0)).comp hts hi)
    have hun : Primrec fun q : Q => q.1.2.getD (q.2 + 1) none :=
      (Primrec.list_getD none).comp hprev (Primrec.succ.comp hi)
    have hbin : Primrec fun q : Q =>
        match q.1.2.getD (q.2 + 1) none with
        | some j => q.1.2.getD j none
        | none => none :=
      (Primrec.option_casesOn hun (Primrec.const none)
        ((Primrec.list_getD none).comp (hprev.comp Primrec.fst) Primrec.snd).to₂).of_eq
        fun q => by cases q.1.2.getD (q.2 + 1) none <;> rfl
    exact Primrec.ite (Primrec.nat_lt.comp hi (Primrec.list_length.comp hts))
      (Primrec.ite (Primrec.eq.comp hk (Primrec.const 0)) (Primrec.option_some.comp (Primrec.succ.comp hi))
        (Primrec.ite (Primrec.eq.comp hk (Primrec.const 1)) hun
          (Primrec.ite (Primrec.eq.comp hk (Primrec.const 2)) hbin (Primrec.const none))))
      (Primrec.const none)
  have hstep : Primrec₂ parseEndStep :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)))
      hcell.to₂
  have hinit : Primrec fun ts : List Token => (List.range (ts.length + 1)).map fun _ => (none : Option ℕ) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
      (Primrec.const none).to₂
  have hend : Primrec fun ts : List Token => parseEndIdx ts ts.length :=
    Primrec.list_foldl (Primrec.list_range.comp Primrec.list_length) hinit
      (hstep.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).to₂
  exact Primrec.ite
    (Primrec.eq.comp ((Primrec.list_getD none).comp hend (Primrec.const 0))
      (Primrec.option_some.comp Primrec.list_length))
    (Primrec.const true) (Primrec.const false)

lemma parseEndIdx_spec (ts : List Token) (fuel : ℕ) :
    (parseEndIdx ts fuel).length = ts.length + 1 ∧
      ∀ i ≤ ts.length,
        (∀ j, (parseEndIdx ts fuel).getD i none = some j →
          j ≤ ts.length ∧ ∃ φ, parseAux fuel (ts.drop i) = some (φ, ts.drop j)) ∧
        ((parseEndIdx ts fuel).getD i none = none → parseAux fuel (ts.drop i) = none) := by
  induction fuel with
  | zero =>
    refine ⟨by simp [parseEndIdx, iterNat], fun i hi => ⟨fun j hj => ?_, fun _ => rfl⟩⟩
    rw [getD_eq_getElem _ none i (by simp [parseEndIdx, iterNat]; omega)] at hj
    simp [parseEndIdx, iterNat] at hj
  | succ fuel ih =>
    rcases ih with ⟨hlen_prev, hprev_spec⟩
    have hlen_cur : (parseEndIdx ts (fuel + 1)).length = ts.length + 1 := by
      rw [parseEndIdx, iterNat_succ]; simp [parseEndStep]
    refine ⟨hlen_cur, fun i hi => ?_⟩
    have hget_cur : (parseEndIdx ts (fuel + 1)).getD i none =
        if i < ts.length then
          let k := tokKind (ts.getD i (99, 0, 0))
          if k = 0 then some (i + 1)
          else if k = 1 then (parseEndIdx ts fuel).getD (i + 1) none
          else if k = 2 then
            match (parseEndIdx ts fuel).getD (i + 1) none with
            | some j => (parseEndIdx ts fuel).getD j none
            | none => none
          else none
        else none := by
      have hstep_eq : parseEndIdx ts (fuel + 1) = parseEndStep ts (parseEndIdx ts fuel) :=
        iterNat_succ _ _ _
      rw [hstep_eq]
      unfold parseEndStep
      rw [getD_eq_getElem _ none i (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range]
      cases (parseEndIdx ts fuel).getD (i + 1) none <;> rfl
    rw [hget_cur]
    by_cases hilt : i < ts.length
    · rw [if_pos hilt]
      have hdrop_i : ts.drop i = ts[i] :: ts.drop (i + 1) := List.drop_eq_getElem_cons hilt
      have hgd_i : ts.getD i (99, 0, 0) = ts[i] := getD_eq_getElem ts (99, 0, 0) i hilt
      rw [hgd_i, hdrop_i]
      rcases hti : ts[i] with ⟨tag, a, b⟩
      -- Helper for leaf, unary, binary cases
      have hleaf : ∀ φ0 : Formula ℕ ℕ ℕ ℕ,
          parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = some (φ0, ts.drop (i + 1)) →
          tokKind (tag, a, b) = 0 →
          (∀ j, some (i + 1) = some j → j ≤ ts.length ∧
            ∃ φ, parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = some (φ, ts.drop j)) ∧
          (some (i + 1) = none → parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = none) := by
        intro φ0 hp _
        refine ⟨fun j hj => ?_, fun hn => by cases hn⟩
        cases Option.some.inj hj
        exact ⟨by omega, φ0, hp⟩
      have hunary : ∀ c : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ,
          parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) =
            (match parseAux fuel (ts.drop (i + 1)) with
             | some (φ, r) => some (c φ, r)
             | none => none) →
          ((∀ j, (parseEndIdx ts fuel).getD (i + 1) none = some j →
            j ≤ ts.length ∧ ∃ φ, parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = some (φ, ts.drop j)) ∧
           ((parseEndIdx ts fuel).getD (i + 1) none = none →
            parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = none)) := by
        intro c hp
        obtain ⟨hs_p, hn_p⟩ := hprev_spec (i + 1) (by omega)
        refine ⟨fun j hj => ?_, fun hn => by rw [hp, hn_p hn]⟩
        obtain ⟨hj_le, φ1, hφ1⟩ := hs_p j hj
        exact ⟨hj_le, c φ1, by rw [hp, hφ1]⟩
      have hbinary : ∀ c : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ,
          parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) =
            (match parseAux fuel (ts.drop (i + 1)) with
             | some (φ, r) =>
               match parseAux fuel r with
               | some (ψ, r') => some (c φ ψ, r')
               | none => none
             | none => none) →
          ((∀ k, (match (parseEndIdx ts fuel).getD (i + 1) none with
                  | some j => (parseEndIdx ts fuel).getD j none
                  | none => none) = some k →
            k ≤ ts.length ∧ ∃ φ, parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = some (φ, ts.drop k)) ∧
           ((match (parseEndIdx ts fuel).getD (i + 1) none with
             | some j => (parseEndIdx ts fuel).getD j none
             | none => none) = none →
            parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = none)) := by
        intro c hp
        obtain ⟨hs_p, hn_p⟩ := hprev_spec (i + 1) (by omega)
        cases h1 : (parseEndIdx ts fuel).getD (i + 1) none with
        | none =>
          dsimp only
          exact ⟨(fun _ hk => by cases hk), (fun _ => by rw [hp, hn_p h1])⟩
        | some j =>
          dsimp only
          obtain ⟨hj_le, φ1, hφ1⟩ := hs_p j h1
          obtain ⟨hs_j, hn_j⟩ := hprev_spec j hj_le
          refine ⟨fun k hk => ?_, fun hn => ?_⟩
          · obtain ⟨hk_le, ψ1, hψ1⟩ := hs_j k hk
            refine ⟨hk_le, c φ1 ψ1, ?_⟩
            rw [hp, hφ1]; dsimp only; rw [hψ1]
          · rw [hp, hφ1]; dsimp only; rw [hn_j hn]
      by_cases htag : tag ≤ 12
      · interval_cases tag
        · -- tag = 0
          by_cases ha12 : a = 1 ∨ a = 2
          · rcases ha12 with rfl | rfl
            · simpa [tokKind] using hleaf (.inp1 b) rfl rfl
            · simpa [tokKind] using hleaf (.inp2 b) rfl rfl
          · have hk3 : tokKind (0, a, b) = 3 := by simp [tokKind, ha12]
            have hp_n : parseAux (fuel + 1) ((0, a, b) :: ts.drop (i + 1)) = none := by
              unfold parseAux; rcases a with _ | _ | _ | a' <;> simp at ha12 ⊢
            simp [hk3, hp_n]
        · -- tag = 1
          by_cases ha12 : a = 1 ∨ a = 2
          · rcases ha12 with rfl | rfl
            · simpa [tokKind] using hleaf (.out1 b) rfl rfl
            · simpa [tokKind] using hleaf (.out2 b) rfl rfl
          · have hk3 : tokKind (1, a, b) = 3 := by simp [tokKind, ha12]
            have hp_n : parseAux (fuel + 1) ((1, a, b) :: ts.drop (i + 1)) = none := by
              unfold parseAux; rcases a with _ | _ | _ | a' <;> simp at ha12 ⊢
            simp [hk3, hp_n]
        · -- tag = 2
          by_cases ha2 : a ≤ 2
          · interval_cases a
            · simpa [tokKind] using hleaf (.graph .oneToTwo) rfl rfl
            · simpa [tokKind] using hleaf (.graph .both) rfl rfl
            · simpa [tokKind] using hleaf (.graph .twoToOne) rfl rfl
          · have hk3 : tokKind (2, a, b) = 3 := by simp [tokKind, ha2]
            have hp_n : parseAux (fuel + 1) ((2, a, b) :: ts.drop (i + 1)) = none := by
              unfold parseAux; rcases a with _ | _ | _ | a' <;> simp at ha2 ⊢
            simp [hk3, hp_n]
        · simpa [tokKind] using hunary .next rfl
        · simpa [tokKind] using hunary .eventually rfl
        · simpa [tokKind] using hunary .always rfl
        · simpa [tokKind] using hbinary .untl rfl
        · simpa [tokKind] using hbinary .weakUntil rfl
        · simpa [tokKind] using hunary .neg rfl
        · simpa [tokKind] using hbinary .or rfl
        · simpa [tokKind] using hbinary .and rfl
        · simpa [tokKind] using hbinary .imp rfl
        · simpa [tokKind] using hbinary .iff rfl
      · have hne : tag ≠ 0 ∧ tag ≠ 1 ∧ tag ≠ 2 ∧ tag ≠ 3 ∧ tag ≠ 4 ∧ tag ≠ 5 ∧ tag ≠ 6 ∧
            tag ≠ 7 ∧ tag ≠ 8 ∧ tag ≠ 9 ∧ tag ≠ 10 ∧ tag ≠ 11 ∧ tag ≠ 12 := by omega
        have hk3 : tokKind (tag, a, b) = 3 := by simp [tokKind, hne]
        have hp_n : parseAux (fuel + 1) ((tag, a, b) :: ts.drop (i + 1)) = none := by
          unfold parseAux
          match tag with
          | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => omega
          | _ + 13 => rfl
        simp [hk3, hp_n]
    · rw [if_neg hilt]
      have hieq : i = ts.length := by omega
      subst hieq
      simp [parseAux]

lemma parseOk_iff_exists_parse (ts : List Token) :
    parseOk ts = true ↔ ∃ φ, parse ts = some φ := by
  unfold parseOk parse
  simp only [decide_eq_true_eq]
  obtain ⟨_, hspec⟩ := parseEndIdx_spec ts ts.length
  obtain ⟨hs, hn⟩ := hspec 0 (Nat.zero_le _)
  simp only [List.drop_zero] at hs hn
  constructor
  · intro heq
    obtain ⟨_, φ, hφ⟩ := hs ts.length heq
    rw [List.drop_length] at hφ
    exact ⟨φ, by rw [hφ]⟩
  · rintro ⟨φ, hφ⟩
    cases hget : (parseEndIdx ts ts.length).getD 0 none with
    | none => rw [hn hget] at hφ; cases hφ
    | some j =>
      obtain ⟨hj_le, ψ, hψ⟩ := hs j hget
      rw [hψ] at hφ
      cases hdrop : ts.drop j with
      | nil =>
        have hj_ge : ts.length ≤ j := List.drop_eq_nil_iff.mp hdrop
        exact congrArg some (by omega)
      | cons _ _ =>
        rw [hdrop] at hφ; cases hφ

@[simp] lemma andBool_eq (a b : Bool) : andBool a b = (a && b) := by cases a <;> cases b <;> rfl

@[simp] lemma orBool_eq (a b : Bool) : orBool a b = (a || b) := by cases a <;> cases b <;> rfl

@[simp] lemma notBool_eq (a : Bool) : notBool a = !a := by cases a <;> rfl

lemma primrec₂_andBool : Primrec₂ andBool :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) Primrec.snd (Primrec.const false)

lemma primrec₂_orBool : Primrec₂ orBool :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) (Primrec.const true) Primrec.snd

lemma memNat_iff (x : ℕ) (l : List ℕ) : memNat x l = true ↔ x ∈ l := by
  suffices ∀ (b : Bool),
      l.foldl (fun acc y => orBool acc (decide (y = x))) b = true ↔ b = true ∨ x ∈ l by
    simpa [memNat] using this false
  induction l with
  | nil => intro b; simp
  | cons y ys ih =>
    intro b
    rw [List.foldl_cons, ih]
    simp only [orBool_eq, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    tauto

lemma primrec₂_memNat : Primrec₂ memNat :=
  Primrec.list_foldl Primrec.snd (Primrec.const false)
    (primrec₂_orBool.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.ite
        (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.const true) (Primrec.const false))).to₂

lemma filter_primrec {X α : Type} [Primcodable X] [Primcodable α]
    {xs : X → List α} {p : X → α → Bool}
    (hxs : Primrec xs) (hp : Primrec fun q : X × α => p q.1 q.2) :
    Primrec fun x : X => (xs x).filter (p x) :=
  (Primrec.list_flatMap hxs
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const true))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const [])).to₂).of_eq fun x => by
    induction xs x with
    | nil => rfl
    | cons a l ih =>
      simp only [List.filter_cons, List.flatMap_cons]
      cases p x a <;> simp [ih]

@[simp] lemma cIdxOf_nil {α : Type} [DecidableEq α] (x : α) : cIdxOf ([] : List α) x = 0 := rfl

@[simp] lemma cIdxOf_cons {α : Type} [DecidableEq α] (y : α) (ys : List α) (x : α) :
    cIdxOf (y :: ys) x = if x = y then 0 else cIdxOf ys x + 1 := rfl

lemma primrec₂_cIdxOf {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (cIdxOf (α := α)) :=
  Primrec.list_foldr Primrec.fst (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂

lemma cIdxOf_lt_and_getElem {α : Type} [DecidableEq α] {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ hlt : cIdxOf xs x < xs.length, xs[cIdxOf xs x]'hlt = x := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy
      exact ⟨by simp, by simp⟩
    · rcases List.mem_cons.mp hx with rfl | htl
      · exact False.elim (hxy rfl)
      · obtain ⟨hlt, heq⟩ := ih htl
        have hc : cIdxOf (y :: ys) x = cIdxOf ys x + 1 := by simp [hxy]
        refine ⟨by rw [hc]; exact Nat.succ_lt_succ hlt, ?_⟩
        simp only [hc, List.getElem_cons_succ, heq]

lemma dedupList_length_le {α : Type} [DecidableEq α] (xs : List α) :
    (dedupList xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [dedupList]
  | cons x xs ih =>
    change (if x ∈ dedupList xs then dedupList xs else x :: dedupList xs).length ≤ xs.length + 1
    split_ifs
    · omega
    · simp only [List.length_cons]; omega

lemma nodup_wordsOf {α : Type} {choices : List α} (hnd : choices.Nodup) :
    ∀ n : ℕ, (wordsOf choices n).Nodup
  | 0 => by simp [wordsOf]
  | n + 1 => by
    have hsec : ∀ (l : List (List α)), (∀ c ∈ l, c.Nodup) → l.sections.Nodup := by
      intro l hl
      induction l with
      | nil => simp [List.sections]
      | cons c cs ih =>
        have hc_nd : c.Nodup := hl c (List.mem_cons.mpr (Or.inl rfl))
        have hcs_nd : cs.sections.Nodup :=
          ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        simp only [List.sections]
        rw [List.nodup_flatMap]
        refine ⟨fun tail _ => hc_nd.map (fun a1 a2 hcons => (List.cons.inj hcons).1), ?_⟩
        refine hcs_nd.pairwise_of_forall_ne fun t1 ht1 t2 ht2 hne => ?_
        unfold Function.onFun
        rw [List.disjoint_left]
        intro w hw1 hw2
        obtain ⟨a1, _, rfl⟩ := List.mem_map.mp hw1
        obtain ⟨a2, _, heq⟩ := List.mem_map.mp hw2
        exact hne (List.cons.inj heq).2.symm
    exact hsec _ (fun c hc => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc; exact hnd)

lemma wordsOf_length {α : Type} (choices : List α) :
    ∀ n : ℕ, (wordsOf choices n).length = choices.length ^ n := by
  have hsec_len : ∀ l : List (List α), l.sections.length = (l.map List.length).prod := by
    intro l
    induction l with
    | nil => simp [List.sections]
    | cons c cs ih =>
      simp only [List.sections, List.length_flatMap,
        List.length_map, List.map_const', ih, List.map_cons, List.prod_cons, List.sum_replicate,
        smul_eq_mul, Nat.mul_comm]
  intro n
  rw [wordsOf, hsec_len]
  simp

lemma list_zip_primrec {α β : Type} [Primcodable α] [Primcodable β] (da : α) (db : β) :
    Primrec₂ (List.zip (α := α) (β := β)) := by
  have hlen : Primrec fun p : List α × List β => min p.1.length p.2.length :=
    Primrec.nat_min.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)
  have hf : Primrec fun p : List α × List β =>
      (List.range (min p.1.length p.2.length)).map fun i => (p.1.getD i da, p.2.getD i db) :=
    Primrec.list_map (Primrec.list_range.comp hlen)
      (((Primrec.list_getD da).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
        ((Primrec.list_getD db).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  refine hf.of_eq fun ⟨xs, ys⟩ => ?_
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    simp only [List.length_map, List.length_range] at hi1
    have hix : i < xs.length := lt_of_lt_of_le hi1 (min_le_left _ _)
    have hiy : i < ys.length := lt_of_lt_of_le hi1 (min_le_right _ _)
    simp only [List.getElem_map, List.getElem_range, List.getElem_zip]
    rw [getD_eq_getElem xs da i hix, getD_eq_getElem ys db i hiy]

def stepCompIdxMat (n : ℕ) (mat : List Bool) (cur : List ℕ) : List ℕ :=
  (List.range n).filter fun y =>
    orBool (memNat y cur)
      (cur.foldl (fun acc x => orBool acc (mat.getD (x * n + y) false)) false)

def componentsIdxMat (n : ℕ) (mat : List Bool) : List (List ℕ) :=
  dedupList ((List.range n).map fun i => iterNat (stepCompIdxMat n mat) n [i])

lemma primrec₂_componentsIdxMat : Primrec₂ componentsIdxMat := by
  let Q0 := ℕ × List Bool
  let Q1 := (Q0 × List ℕ) × ℕ
  have hfold : Primrec fun q : Q1 =>
      q.1.2.foldl (fun acc x => orBool acc (q.1.1.2.getD (x * q.1.1.1 + q.2) false)) false := by
    let R := Q1 × (Bool × ℕ)
    have hn : Primrec fun r : R => r.1.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hmat : Primrec fun r : R => r.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hy : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
    have hacc : Primrec fun r : R => r.2.1 := Primrec.fst.comp Primrec.snd
    have hx : Primrec fun r : R => r.2.2 := Primrec.snd.comp Primrec.snd
    have hidx : Primrec fun r : R => r.2.2 * r.1.1.1.1 + r.1.2 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp hx hn) hy
    exact Primrec.list_foldl (Primrec.snd.comp Primrec.fst) (Primrec.const false)
      (primrec₂_orBool.comp hacc ((Primrec.list_getD false).comp hmat hidx)).to₂
  have hstep : Primrec fun p : Q0 × List ℕ => stepCompIdxMat p.1.1 p.1.2 p.2 :=
    filter_primrec (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
      (primrec₂_orBool.comp
        (primrec₂_memNat.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
        hfold)
  have hcomp : Primrec fun p : Q0 × ℕ => iterNat (stepCompIdxMat p.1.1 p.1.2) p.1.1 [p.2] :=
    Primrec.list_foldl
      (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (hstep.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))).to₂
  exact dedupList_primrec.comp
    (Primrec.list_map
      (Primrec.list_range.comp Primrec.fst)
      hcomp.to₂)

lemma componentsIdx_eq_mat {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) :
    componentsIdx inh S adj =
      componentsIdxMat S.length
        ((List.range S.length).flatMap fun x =>
          (List.range S.length).map fun y => adj (S.getD x inh) (S.getD y inh)) := by
  let n := S.length
  let mat := (List.range n).flatMap fun x =>
    (List.range n).map fun y => adj (S.getD x inh) (S.getD y inh)
  have hmat_get : ∀ x < n, ∀ y < n,
      mat.getD (x * n + y) false = adj (S.getD x inh) (S.getD y inh) := by
    intro x hx y hy
    have hrec : ∀ R, x < R →
        ((List.range R).flatMap fun a =>
          (List.range n).map fun b => adj (S.getD a inh) (S.getD b inh)).getD (x * n + y) false =
          adj (S.getD x inh) (S.getD y inh) := by
      intro R hlt
      induction R with
      | zero => cases hlt
      | succ R ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        have hlp : ((List.range R).flatMap fun a =>
            (List.range n).map fun b => adj (S.getD a inh) (S.getD b inh)).length = R * n := by
          simp [List.length_flatMap, List.map_const']
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hr_lt
        · rw [getD_eq_getElem _ false _ (by rw [List.length_append, hlp]; simp [hy]),
            List.getElem_append_right (by omega)]
          simp only [List.getElem_map, List.getElem_range, hlp, Nat.add_sub_cancel_left]
        · have hlt_p : x * n + y < R * n := by
            have h1 : x + 1 ≤ R := hr_lt
            calc x * n + y < x * n + n := Nat.add_lt_add_left hy _
              _ = (x + 1) * n := by ring
              _ ≤ R * n := Nat.mul_le_mul_right n h1
          rw [getD_eq_getElem _ false _ (by rw [List.length_append, hlp]; simp; omega),
            List.getElem_append_left (by omega), ← getD_eq_getElem _ false _ (by omega)]
          exact ih hr_lt
    exact hrec n hx
  have hstep_eq : ∀ cur : List ℕ, (∀ x ∈ cur, x < n) →
      stepCompIdx inh S adj cur = stepCompIdxMat n mat cur ∧
        ∀ z ∈ stepCompIdx inh S adj cur, z < n := by
    intro cur hcur
    refine ⟨?_, fun z hz => List.mem_range.mp (List.mem_filter.mp hz).1⟩
    unfold stepCompIdx stepCompIdxMat
    apply List.filter_congr
    intro y hy
    have hy_lt : y < n := List.mem_range.mp hy
    congr 1
    have hfold_eq : ∀ (xs : List ℕ), (∀ x ∈ xs, x < n) → ∀ b : Bool,
        xs.foldl (fun acc x => orBool acc (adj (S.getD x inh) (S.getD y inh))) b =
          xs.foldl (fun acc x => orBool acc (mat.getD (x * n + y) false)) b := by
      intro xs hxs
      induction xs with
      | nil => intro b; rfl
      | cons x xs ih =>
        intro b
        rw [List.foldl_cons, List.foldl_cons,
          hmat_get x (hxs x (List.mem_cons.mpr (Or.inl rfl))) y hy_lt]
        exact ih (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) _
    exact hfold_eq cur hcur false
  have hiter_eq : ∀ (m : ℕ) (i : ℕ), i < n →
      iterNat (stepCompIdx inh S adj) m [i] = iterNat (stepCompIdxMat n mat) m [i] ∧
        ∀ x ∈ iterNat (stepCompIdx inh S adj) m [i], x < n := by
    intro m i hi
    induction m with
    | zero =>
      exact ⟨rfl, fun x hx => by
        simp only [iterNat, List.range_zero, List.foldl_nil, List.mem_singleton] at hx
        rwa [hx]⟩
    | succ m ih =>
      rw [iterNat_succ, iterNat_succ]
      obtain ⟨heq_m, hlt_m⟩ := ih
      obtain ⟨heq_s, hlt_s⟩ := hstep_eq _ hlt_m
      rw [← heq_m]
      exact ⟨heq_s, hlt_s⟩
  unfold componentsIdx componentsIdxMat compIdxOf
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hiter_eq n i (List.mem_range.mp hi)).1

lemma foldl_orBool_adj_iff {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    (cur : List ℕ) (y : ℕ) :
    cur.foldl (fun acc x => orBool acc (adj (S.getD x inh) (S.getD y inh))) false = true ↔
      ∃ x ∈ cur, adj (S.getD x inh) (S.getD y inh) = true := by
  suffices ∀ b : Bool,
      cur.foldl (fun acc x => orBool acc (adj (S.getD x inh) (S.getD y inh))) b = true ↔
        b = true ∨ ∃ x ∈ cur, adj (S.getD x inh) (S.getD y inh) = true by
    simpa using this false
  induction cur with
  | nil => intro b; simp
  | cons x xs ih =>
    intro b
    rw [List.foldl_cons, ih]
    simp only [orBool_eq, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((hb | hx) | ⟨z, hz, hza⟩)
      · exact Or.inl hb
      · exact Or.inr ⟨x, Or.inl rfl, hx⟩
      · exact Or.inr ⟨z, Or.inr hz, hza⟩
    · rintro (hb | ⟨z, rfl | hz, hza⟩)
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr hza)
      · exact Or.inr ⟨z, hz, hza⟩

lemma mem_stepCompIdx_iff {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    (cur : List ℕ) (y : ℕ) :
    y ∈ stepCompIdx inh S adj cur ↔
      y < S.length ∧ (y ∈ cur ∨ ∃ x ∈ cur, adj (S.getD x inh) (S.getD y inh) = true) := by
  unfold stepCompIdx
  rw [List.mem_filter, List.mem_range, orBool_eq, Bool.or_eq_true,
    memNat_iff, foldl_orBool_adj_iff]

lemma mem_compIdxOf_iff {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    {i : ℕ} (hi : i < S.length) (y : ℕ) :
    y ∈ compIdxOf inh S adj i ↔
      y < S.length ∧
        Relation.ReflTransGen
          (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i y := by
  classical
  let N := S.length
  let R := fun a b : ℕ => a < N ∧ b < N ∧ adj (S.getD a inh) (S.getD b inh) = true
  let iter : ℕ → List ℕ := fun m => iterNat (stepCompIdx inh S adj) m [i]
  have hsub : ∀ m x, x ∈ iter m → x < N ∧ Relation.ReflTransGen R i x := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp only [iter, iterNat, List.range_zero, List.foldl_nil, List.mem_singleton] at hx
      subst hx
      exact ⟨hi, .refl⟩
    | succ m ih =>
      intro x hx
      have hx' : x ∈ stepCompIdx inh S adj (iter m) := by simpa [iter, iterNat_succ] using hx
      rw [mem_stepCompIdx_iff] at hx'
      rcases hx' with ⟨hx_lt, hmem | ⟨z, hz, hadj⟩⟩
      · exact ih x hmem
      · obtain ⟨hz_lt, hrz⟩ := ih z hz
        exact ⟨hx_lt, hrz.tail ⟨hz_lt, hx_lt, hadj⟩⟩
  have hmono : ∀ m x, x ∈ iter m → x ∈ iter (m + 1) := by
    intro m x hx
    have hx_lt := (hsub m x hx).1
    have hstep_m : iter (m + 1) = stepCompIdx inh S adj (iter m) := iterNat_succ _ _ _
    rw [hstep_m, mem_stepCompIdx_iff]
    exact ⟨hx_lt, Or.inl hx⟩
  have hmono_le : ∀ {m1 m2}, m1 ≤ m2 → ∀ x, x ∈ iter m1 → x ∈ iter m2 := by
    intro m1 m2 hle
    induction m2 with
    | zero =>
      have hm0 : m1 = 0 := by omega
      subst hm0; exact fun _ h => h
    | succ m2 ih =>
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact fun _ h => h
      · exact fun x hx => hmono m2 x (ih (by omega) x hx)
  constructor
  · intro hy
    exact hsub N y hy
  · rintro ⟨hy_lt, hreach⟩
    have hstab : ∃ m ≤ N, ∀ x, x ∈ iter (m + 1) ↔ x ∈ iter m := by
      by_contra hnostab
      have hgrow : ∀ m ≤ N, ∃ x, x ∈ iter (m + 1) ∧ x ∉ iter m := by
        intro m hm
        by_contra hno
        apply hnostab
        refine ⟨m, hm, fun x => ⟨fun hx1 => ?_, hmono m x⟩⟩
        by_contra hnot
        exact hno ⟨x, hx1, hnot⟩
      have hcard_lb : ∀ k ≤ N + 1, k + 1 ≤ (iter k).toFinset.card := by
        intro k hk
        induction k with
        | zero =>
          have hi0 : i ∈ (iter 0).toFinset := List.mem_toFinset.mpr (by simp [iter, iterNat])
          exact Finset.card_pos.mpr ⟨i, hi0⟩
        | succ k ih =>
          have hk_le : k ≤ N := by omega
          obtain ⟨x, hx1, hx0⟩ := hgrow k hk_le
          have hss : (iter k).toFinset ⊂ (iter (k + 1)).toFinset := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun z hz => List.mem_toFinset.mpr (hmono k z (List.mem_toFinset.mp hz)), ?_⟩
            intro heq
            exact hx0 (List.mem_toFinset.mp (heq ▸ List.mem_toFinset.mpr hx1))
          have hlt_c := Finset.card_lt_card hss
          have ih' := ih (by omega)
          omega
      have hsub_range : (iter N).toFinset ⊆ Finset.range N := by
        intro z hz
        exact Finset.mem_range.mpr (hsub N z (List.mem_toFinset.mp hz)).1
      have hub : (iter N).toFinset.card ≤ N := by
        simpa using Finset.card_le_card hsub_range
      have hlb := hcard_lb N (by omega)
      omega
    rcases hstab with ⟨m, hm_le, hfix⟩
    have hi_in_m : i ∈ iter m := hmono_le (Nat.zero_le m) i (by simp [iter, iterNat])
    have hclosed_m : ∀ {a b}, a ∈ iter m → R a b → b ∈ iter m := by
      intro a b ha hr
      apply (hfix b).mp
      have hstep_m : iter (m + 1) = stepCompIdx inh S adj (iter m) := iterNat_succ _ _ _
      rw [hstep_m, mem_stepCompIdx_iff]
      exact ⟨hr.2.1, Or.inr ⟨a, ha, hr.2.2⟩⟩
    clear hy_lt
    have hy_in_m : y ∈ iter m := by
      induction hreach with
      | refl => exact hi_in_m
      | tail _ hedge ih => exact hclosed_m ih hedge
    exact hmono_le hm_le y hy_in_m

lemma compIdxOf_nodup_and_lt {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    {i : ℕ} (hi : i < S.length) :
    (compIdxOf inh S adj i).Nodup ∧ i ∈ compIdxOf inh S adj i ∧
      (compIdxOf inh S adj i).length ≤ S.length ∧
      ∀ y ∈ compIdxOf inh S adj i, y < S.length := by
  have hpos : S.length = (S.length - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ S.length)).symm
  have hnd : (compIdxOf inh S adj i).Nodup := by
    unfold compIdxOf
    rw [hpos, iterNat_succ]
    exact List.Nodup.filter _ List.nodup_range
  have hlen : (compIdxOf inh S adj i).length ≤ S.length := by
    unfold compIdxOf
    conv_lhs => rw [hpos, iterNat_succ]
    unfold stepCompIdx
    exact le_trans (List.length_filter_le _ _) (by simp)
  refine ⟨hnd, ?_, hlen, fun y hy => (mem_compIdxOf_iff inh S adj hi y).mp hy |>.1⟩
  rw [mem_compIdxOf_iff inh S adj hi i]
  exact ⟨hi, .refl⟩

lemma compIdxOf_eq_of_reach {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    (hsym : ∀ a < S.length, ∀ b < S.length,
      adj (S.getD a inh) (S.getD b inh) = adj (S.getD b inh) (S.getD a inh))
    {i j : ℕ} (hi : i < S.length) (hj : j < S.length)
    (hreach : Relation.ReflTransGen
      (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i j) :
    compIdxOf inh S adj i = compIdxOf inh S adj j := by
  let R := fun a b : ℕ => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true
  have rev : ∀ {a b}, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b hr
    induction hr with
    | refl => exact .refl
    | tail _ hedge ih =>
      have hs : R _ _ := ⟨hedge.2.1, hedge.1, by rw [hsym _ hedge.2.1 _ hedge.1]; exact hedge.2.2⟩
      exact (Relation.ReflTransGen.single hs).trans ih
  have hpos : S.length = (S.length - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ S.length)).symm
  have hfilter_eq : ∀ k (hk : k < S.length),
      compIdxOf inh S adj k =
        (List.range S.length).filter (fun y => decide (y ∈ compIdxOf inh S adj k)) := by
    intro k hk
    let prev := iterNat (stepCompIdx inh S adj) (S.length - 1) [k]
    have hk_eq : compIdxOf inh S adj k = stepCompIdx inh S adj prev := by
      unfold compIdxOf; conv_lhs => rw [hpos, iterNat_succ]
    have hstep_def : stepCompIdx inh S adj prev =
        (List.range S.length).filter (fun y =>
          orBool (memNat y prev)
            (prev.foldl (fun acc x => orBool acc (adj (S.getD x inh) (S.getD y inh))) false)) := rfl
    conv_lhs => rw [hk_eq, hstep_def]
    apply List.filter_congr
    intro y hy
    have hy_lt : y < S.length := List.mem_range.mp hy
    rw [hk_eq, Bool.eq_iff_iff, orBool_eq, Bool.or_eq_true, memNat_iff, foldl_orBool_adj_iff,
      decide_eq_true_eq, mem_stepCompIdx_iff]
    exact ⟨fun h => ⟨hy_lt, h⟩, fun h => h.2⟩
  rw [hfilter_eq i hi, hfilter_eq j hj]
  apply List.filter_congr
  intro y _
  simp only [decide_eq_decide, mem_compIdxOf_iff inh S adj hi y, mem_compIdxOf_iff inh S adj hj y]
  exact ⟨fun ⟨hyl, hiy⟩ => ⟨hyl, (rev hreach).trans hiy⟩,
    fun ⟨hyl, hjy⟩ => ⟨hyl, hreach.trans hjy⟩⟩

lemma componentsIdx_length_le {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) :
    (componentsIdx inh S adj).length ≤ S.length := by
  calc
    (componentsIdx inh S adj).length ≤ ((List.range S.length).map (compIdxOf inh S adj)).length :=
      dedupList_length_le _
    _ = S.length := by simp

lemma primrec_instK1 : Primrec Instance.k1 := Primrec.fst.comp Primrec.of_equiv

lemma primrec_instK2 : Primrec Instance.k2 := Primrec.fst.comp (Primrec.snd.comp Primrec.of_equiv)

lemma primrec_instM1 : Primrec Instance.m1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv))

lemma primrec_instM2 : Primrec Instance.m2 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)))

lemma sigCard_pos (I : Instance) : 0 < sigCard I := by unfold sigCard; positivity

lemma primrec_sigCard : Primrec sigCard :=
  Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.succ.comp primrec_instK1) (Primrec.succ.comp primrec_instK2))
    (Primrec.const 3)

lemma primrec_decSigG : Primrec decSigG := Primrec.nat_mod.comp Primrec.id (Primrec.const 3)

lemma primrec₂_decSigX2 : Primrec₂ decSigX2 :=
  Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 3))
    (Primrec.succ.comp (primrec_instK2.comp Primrec.fst))

lemma primrec₂_decSigX1 : Primrec₂ decSigX1 :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 3))
      (Primrec.succ.comp (primrec_instK2.comp Primrec.fst)))
    (Primrec.succ.comp (primrec_instK1.comp Primrec.fst))

lemma decSigFields_encSigTyped (I : Instance) (s : Signal I.X1 I.X2) :
    decSigX1 I (encSigTyped I s) = s.1.val ∧
      decSigX2 I (encSigTyped I s) = s.2.1.val ∧
      decSigG (encSigTyped I s) = s.2.2.idx ∧
      decGraph (encSigTyped I s) = s.2.2 := by
  rcases s with ⟨x1, x2, g⟩
  have hg_lt : g.idx < 3 := by cases g <;> decide
  have hdiv3 : ((x1.val * (I.k2 + 1) + x2.val) * 3 + g.idx) / 3 =
      x1.val * (I.k2 + 1) + x2.val := by
    rw [Nat.mul_comm _ 3, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 3),
      Nat.div_eq_of_lt hg_lt, zero_add]
  have hmod3 : ((x1.val * (I.k2 + 1) + x2.val) * 3 + g.idx) % 3 = g.idx := by
    rw [Nat.mul_comm _ 3, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg_lt]
  have hdivK2 : (x1.val * (I.k2 + 1) + x2.val) / (I.k2 + 1) = x1.val := by
    rw [Nat.mul_comm x1.val _, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt x2.isLt, zero_add]
  have hmodK2 : (x1.val * (I.k2 + 1) + x2.val) % (I.k2 + 1) = x2.val := by
    rw [Nat.mul_comm x1.val _, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x2.isLt]
  refine ⟨?_, ?_, hmod3, ?_⟩
  · unfold decSigX1 encSigTyped; dsimp only; rw [hdiv3, hdivK2, Nat.mod_eq_of_lt x1.isLt]
  · unfold decSigX2 encSigTyped; dsimp only; rw [hdiv3, hmodK2]
  · unfold decGraph encSigTyped; dsimp only; rw [hmod3]; cases g <;> rfl

lemma decSigTyped_encSigTyped (I : Instance) (s : Signal I.X1 I.X2) :
    decSigTyped I (encSigTyped I s) = s := by
  obtain ⟨hx1, hx2, _, hg⟩ := decSigFields_encSigTyped I s
  rcases s with ⟨x1, x2, g⟩
  unfold decSigTyped
  ext <;> simp [hx1, hx2, hg]

@[simp] lemma decHist_encHist (I : Instance) (h : List (Signal I.X1 I.X2)) :
    decHist I (encHist I h) = h := by
  simp [decHist, encHist, List.map_map, Function.comp_def, decSigTyped_encSigTyped]

@[simp] lemma decBlock_encBlock (I : Instance) {D : ℕ} (u : Fin D → Signal I.X1 I.X2) :
    decBlock I D (encBlock I u) = u := by
  funext t
  unfold decBlock encBlock encHist
  rw [getD_eq_getElem _ 0 t.val (by simp [t.isLt])]
  simp [decSigTyped_encSigTyped]

lemma primrec₂_nonemptyExtWords : Primrec₂ nonemptyExtWords :=
  Primrec.list_flatMap
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) (Primrec.succ.comp Primrec.snd).to₂)
    (wordsOf_primrec.comp
      (Primrec.list_range.comp (primrec_sigCard.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd).to₂

lemma primrec₂_fullBlocks : Primrec₂ fullBlocks :=
  wordsOf_primrec.comp (Primrec.list_range.comp (primrec_sigCard.comp Primrec.fst)) Primrec.snd

lemma nodup_fullBlocks (I : Instance) (D : ℕ) : (fullBlocks I D).Nodup :=
  nodup_wordsOf List.nodup_range D

lemma length_fullBlocks (I : Instance) (D : ℕ) : (fullBlocks I D).length = (sigCard I) ^ D := by
  simp [fullBlocks, wordsOf_length]

lemma primrec_extStepBool :
    Primrec fun q : Instance × ((Bool × Bool) × (ℕ × ℕ)) => extStepBool q.1 q.2.1 q.2.2 := by
  let Q := Instance × ((Bool × Bool) × (ℕ × ℕ))
  have hI : Primrec fun q : Q => q.1 := Primrec.fst
  have hp1 : Primrec fun q : Q => q.2.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hp2 : Primrec fun q : Q => q.2.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hs : Primrec fun q : Q => q.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs' : Primrec fun q : Q => q.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hg := primrec_decSigG.comp hs
  have hx1 := primrec₂_decSigX1.comp hI hs
  have hx2 := primrec₂_decSigX2.comp hI hs
  have hg' := primrec_decSigG.comp hs'
  have hx1' := primrec₂_decSigX1.comp hI hs'
  have hx2' := primrec₂_decSigX2.comp hI hs'
  have hc1a : Primrec fun q : Q => decide (decSigG q.2.2.2 = 0 ∧ decSigX1 q.1 q.2.2.1 = decSigX1 q.1 q.2.2.2) :=
    Primrec.ite ((Primrec.eq.comp hg' (Primrec.const 0)).and (Primrec.eq.comp hx1 hx1'))
      (Primrec.const true) (Primrec.const false)
  have hc1b : Primrec fun q : Q =>
      decide (decSigG q.2.2.2 ≠ 0 ∧ decSigX1 q.1 q.2.2.1 = decSigX1 q.1 q.2.2.2 ∧
        decSigX2 q.1 q.2.2.1 = decSigX2 q.1 q.2.2.2) :=
    Primrec.ite (((Primrec.eq.comp hg' (Primrec.const 0)).not).and
      ((Primrec.eq.comp hx1 hx1').and (Primrec.eq.comp hx2 hx2')))
      (Primrec.const true) (Primrec.const false)
  have hc2a : Primrec fun q : Q => decide (decSigG q.2.2.2 = 2 ∧ decSigX2 q.1 q.2.2.1 = decSigX2 q.1 q.2.2.2) :=
    Primrec.ite ((Primrec.eq.comp hg' (Primrec.const 2)).and (Primrec.eq.comp hx2 hx2'))
      (Primrec.const true) (Primrec.const false)
  have hc2b : Primrec fun q : Q =>
      decide (decSigG q.2.2.2 ≠ 2 ∧ decSigX2 q.1 q.2.2.1 = decSigX2 q.1 q.2.2.2 ∧
        decSigX1 q.1 q.2.2.1 = decSigX1 q.1 q.2.2.2) :=
    Primrec.ite (((Primrec.eq.comp hg' (Primrec.const 2)).not).and
      ((Primrec.eq.comp hx2 hx2').and (Primrec.eq.comp hx1 hx1')))
      (Primrec.const true) (Primrec.const false)
  have he1 := Primrec.ite (Primrec.eq.comp hg (Primrec.const 0))
    (primrec₂_andBool.comp hc1a hp1)
    (primrec₂_andBool.comp hc1b (primrec₂_andBool.comp hp1 hp2))
  have he2 := Primrec.ite (Primrec.eq.comp hg (Primrec.const 2))
    (primrec₂_andBool.comp hc2a hp2)
    (primrec₂_andBool.comp hc2b (primrec₂_andBool.comp hp2 hp1))
  exact he1.pair he2

lemma primrec_extEqFrom :
    Primrec fun q : (Instance × (Bool × Bool)) × (List ℕ × List ℕ) =>
      extEqFrom q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2 := by
  let Q := (Instance × (Bool × Bool)) × (List ℕ × List ℕ)
  have hw1 : Primrec fun q : Q => q.2.1 := Primrec.fst.comp Primrec.snd
  have hw2 : Primrec fun q : Q => q.2.2 := Primrec.snd.comp Primrec.snd
  have hinit : Primrec fun q : Q => (q.1.2.1, q.1.2.2) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hzip : Primrec fun q : Q => q.2.1.zip q.2.2 := (list_zip_primrec 0 0).comp hw1 hw2
  have hfold : Primrec _ :=
    Primrec.list_foldl hzip hinit
      (primrec_extStepBool.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂
  have hfull : Primrec _ := Primrec.ite
    (Primrec.eq.comp (Primrec.list_length.comp hw1) (Primrec.list_length.comp hw2))
    hfold
    (Primrec.const (false, false))
  exact hfull.of_eq fun _ => rfl

lemma extEqFrom_mono (I : Instance) {b1 b2 b1' b2' : Bool}
    (h1 : b1 = true → b1' = true) (h2 : b2 = true → b2' = true)
    (w1 w2 : List ℕ) :
    ((extEqFrom I b1 b2 w1 w2).1 = true → (extEqFrom I b1' b2' w1 w2).1 = true) ∧
      ((extEqFrom I b1 b2 w1 w2).2 = true → (extEqFrom I b1' b2' w1 w2).2 = true) := by
  unfold extEqFrom
  by_cases hlen : w1.length = w2.length
  · rw [if_pos hlen, if_pos hlen]
    suffices ∀ (zs : List (ℕ × ℕ)) {p p' : Bool × Bool},
        (p.1 = true → p'.1 = true) → (p.2 = true → p'.2 = true) →
        ((zs.foldl (extStepBool I) p).1 = true → (zs.foldl (extStepBool I) p').1 = true) ∧
          ((zs.foldl (extStepBool I) p).2 = true → (zs.foldl (extStepBool I) p').2 = true) from
      this (w1.zip w2) h1 h2
    intro zs
    induction zs with
    | nil => intro p p' hp1 hp2; exact ⟨hp1, hp2⟩
    | cons ss tl ih =>
      intro p p' hp1 hp2
      apply ih
      · unfold extStepBool; dsimp only
        split_ifs <;> simp only [andBool_eq, Bool.and_eq_true] <;> tauto
      · unfold extStepBool; dsimp only
        split_ifs <;> simp only [andBool_eq, Bool.and_eq_true] <;> tauto
  · rw [if_neg hlen, if_neg hlen]; simp

lemma extEqFrom_exact (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)} (hlen : h1.length = h2.length)
    (w1 w2 : List ℕ) :
    extEqFrom I (decide (view1 h1 = view1 h2)) (decide (view2 h1 = view2 h2)) w1 w2 =
      (decide (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2)),
       decide (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2))) := by
  unfold extEqFrom
  by_cases hwlen : w1.length = w2.length
  · rw [if_pos hwlen]
    induction w1 using List.reverseRecOn generalizing w2 with
    | nil =>
      have hw2 : w2 = [] := List.eq_nil_of_length_eq_zero hwlen.symm
      subst hw2; simp [decHist]
    | append_singleton u1 s1 ih =>
      cases w2 using List.reverseRecOn with
      | nil => simp at hwlen
      | append_singleton u2 s2 =>
        have hu : u1.length = u2.length := by simpa using hwlen
        rw [List.zip_append hu, List.zip_cons_cons, List.zip_nil_right,
          List.foldl_append, List.foldl_cons, List.foldl_nil, ih u2 hu]
        have hd1 : decHist I (u1 ++ [s1]) = decHist I u1 ++ [decSigTyped I s1] := by simp [decHist]
        have hd2 : decHist I (u2 ++ [s2]) = decHist I u2 ++ [decSigTyped I s2] := by simp [decHist]
        rw [hd1, hd2, ← List.append_assoc, ← List.append_assoc,
          view1_append_singleton, view1_append_singleton,
          view2_append_singleton, view2_append_singleton]
        unfold decSigTyped extStepBool
        simp only [viewStep1_eq_ite, viewStep2_eq_ite, andBool_eq]
        have hg0 : ∀ s, (decGraph s = .oneToTwo) ↔ decSigG s = 0 := by
          intro s; unfold decGraph decSigG
          have : s % 3 < 3 := Nat.mod_lt _ (by decide)
          set r := s % 3; interval_cases r <;> decide
        have hg2 : ∀ s, (decGraph s = .twoToOne) ↔ decSigG s = 2 := by
          intro s; unfold decGraph decSigG
          have : s % 3 < 3 := Nat.mod_lt _ (by decide)
          set r := s % 3; interval_cases r <;> decide
        apply Prod.ext
        · by_cases hc1 : decSigG s1 = 0 <;> by_cases hc2 : decSigG s2 = 0
          · have e1 : decGraph s1 = .oneToTwo := (hg0 s1).mpr hc1
            have e2 : decGraph s2 = .oneToTwo := (hg0 s2).mpr hc2
            simp [hc1, hc2, e1, e2, Fin.ext_iff]
          · have e1 : decGraph s1 = .oneToTwo := (hg0 s1).mpr hc1
            have e2 : decGraph s2 ≠ .oneToTwo := mt (hg0 s2).mp hc2
            simp [hc1, hc2, e1, e2]
          · have e1 : decGraph s1 ≠ .oneToTwo := mt (hg0 s1).mp hc1
            have e2 : decGraph s2 = .oneToTwo := (hg0 s2).mpr hc2
            simp [hc1, hc2, e1, e2]
          · have e1 : decGraph s1 ≠ .oneToTwo := mt (hg0 s1).mp hc1
            have e2 : decGraph s2 ≠ .oneToTwo := mt (hg0 s2).mp hc2
            rw [Bool.eq_iff_iff]; simp [hc1, hc2, e1, e2, Fin.ext_iff]; tauto
        · by_cases hc1 : decSigG s1 = 2 <;> by_cases hc2 : decSigG s2 = 2
          · have e1 : decGraph s1 = .twoToOne := (hg2 s1).mpr hc1
            have e2 : decGraph s2 = .twoToOne := (hg2 s2).mpr hc2
            simp [hc1, hc2, e1, e2, Fin.ext_iff]
          · have e1 : decGraph s1 = .twoToOne := (hg2 s1).mpr hc1
            have e2 : decGraph s2 ≠ .twoToOne := mt (hg2 s2).mp hc2
            simp [hc1, hc2, e1, e2]
          · have e1 : decGraph s1 ≠ .twoToOne := mt (hg2 s1).mp hc1
            have e2 : decGraph s2 = .twoToOne := (hg2 s2).mpr hc2
            simp [hc1, hc2, e1, e2]
          · have e1 : decGraph s1 ≠ .twoToOne := mt (hg2 s1).mp hc1
            have e2 : decGraph s2 ≠ .twoToOne := mt (hg2 s2).mp hc2
            rw [Bool.eq_iff_iff]; simp [hc1, hc2, e1, e2, Fin.ext_iff]; tauto
  · rw [if_neg hwlen]
    have hne1 : view1 (h1 ++ decHist I w1) ≠ view1 (h2 ++ decHist I w2) := by
      intro heq
      have hd := congrArg vdepth heq
      rw [(vdepth_views _).1, (vdepth_views _).1] at hd
      simp only [List.length_append, decHist, List.length_map, hlen] at hd
      exact hwlen (Nat.add_left_cancel hd)
    have hne2 : view2 (h1 ++ decHist I w1) ≠ view2 (h2 ++ decHist I w2) := by
      intro heq
      have hd := congrArg vdepth heq
      rw [(vdepth_views _).2, (vdepth_views _).2] at hd
      simp only [List.length_append, decHist, List.length_map, hlen] at hd
      exact hwlen (Nat.add_left_cancel hd)
    simp [hne1, hne2]

lemma extEqFrom_of_hom (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)} (hlen : h1.length = h2.length)
    {b1 b2 : Bool} (hb1 : view1 h1 = view1 h2 → b1 = true) (hb2 : view2 h1 = view2 h2 → b2 = true)
    (w1 w2 : List ℕ) :
    (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).1 = true) ∧
      (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).2 = true) := by
  have hm := extEqFrom_mono I
    (b1 := decide (view1 h1 = view1 h2)) (b2 := decide (view2 h1 = view2 h2))
    (fun h => hb1 (of_decide_eq_true h)) (fun h => hb2 (of_decide_eq_true h)) w1 w2
  rw [extEqFrom_exact I hlen w1 w2] at hm
  exact ⟨fun hv1 => hm.1 (decide_eq_true hv1), fun hv2 => hm.2 (decide_eq_true hv2)⟩

lemma ctxBlockCard_pos (c : SymCtx) : 0 < ctxBlockCard c := by
  unfold ctxBlockCard; rw [myPow_eq]; exact Nat.pow_pos (sigCard_pos (ctxI c))

lemma ctxBRed_pos (c : SymCtx) : 0 < ctxBRed c := by
  unfold ctxBRed
  rw [myPow_eq]
  exact Nat.mul_pos (Nat.pow_pos (by unfold ctxQBCard; omega)) (ctxBlockCard_pos c)

lemma ctxBFull_pos (c : SymCtx) : 0 < ctxBFull c :=
  Nat.mul_pos (ctxBRed_pos c) (ctxBlockCard_pos c)

lemma primrec_ctxI : Primrec ctxI := Primrec.fst

lemma primrec_ctxD : Primrec ctxD := Primrec.succ.comp (Primrec.fst.comp Primrec.snd)

lemma primrec_ctxBCode : Primrec ctxBCode := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma primrec_ctxLive : Primrec ctxLive := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

lemma primrec_ctxQBCard : Primrec ctxQBCard := Primrec.succ.comp (Primrec.fst.comp primrec_ctxBCode)

lemma primrec_ctxBlockCard : Primrec ctxBlockCard :=
  primrec₂_myPow.comp (primrec_sigCard.comp primrec_ctxI) primrec_ctxD

lemma primrec_ctxBRed : Primrec ctxBRed :=
  (Primrec.nat_mul.comp
    (primrec₂_myPow.comp (Primrec.nat_add.comp (Primrec.const 1) primrec_ctxQBCard) primrec_ctxBlockCard)
    primrec_ctxBlockCard).of_eq fun _ => rfl

lemma primrec_ctxBFull : Primrec ctxBFull :=
  (Primrec.nat_mul.comp primrec_ctxBRed primrec_ctxBlockCard).of_eq fun _ => rfl

lemma primrec_eq1At : Primrec fun q : SymPosCode × (ℕ × ℕ) => eq1At q.1 q.2.1 q.2.2 :=
  (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))

lemma primrec_eq2At : Primrec fun q : SymPosCode × (ℕ × ℕ) => eq2At q.1 q.2.1 q.2.2 :=
  (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))

lemma primrec₂_stateAt : Primrec₂ stateAt :=
  (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd

lemma primrec_allSymPos : Primrec allSymPos := by
  have hks : Primrec fun c : SymCtx => (List.range (ctxBFull c)).map (· + 1) :=
    Primrec.list_map (Primrec.list_range.comp primrec_ctxBFull) (Primrec.succ.comp Primrec.snd).to₂
  have he1s : Primrec fun q : SymCtx × ℕ => wordsOf [false, true] (q.2 * q.2) :=
    wordsOf_primrec.comp (Primrec.const [false, true]) (Primrec.nat_mul.comp Primrec.snd Primrec.snd)
  have he2s : Primrec fun q : (SymCtx × ℕ) × List Bool => wordsOf [false, true] (q.1.2 * q.1.2) :=
    he1s.comp Primrec.fst
  have hsts : Primrec fun q : ((SymCtx × ℕ) × List Bool) × List Bool =>
      wordsOf (List.range (ctxQBCard q.1.1.1)) q.1.1.2 :=
    wordsOf_primrec.comp
      (Primrec.list_range.comp (primrec_ctxQBCard.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.list_flatMap hks
    (Primrec.list_flatMap he1s
      (Primrec.list_flatMap he2s
        (Primrec.list_map hsts
          ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
            ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
              ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂).to₂).to₂).to₂

lemma primrec₂_allSymActsFor : Primrec₂ allSymActsFor := by
  let Q := SymCtx × SymPosCode
  have hk : Primrec fun q : Q => q.2.1 := Primrec.fst.comp Primrec.snd
  have hNW : Primrec fun q : Q => (nonemptyExtWords (ctxI q.1) (ctxD q.1)).length :=
    Primrec.list_length.comp
      (primrec₂_nonemptyExtWords.comp (primrec_ctxI.comp Primrec.fst) (primrec_ctxD.comp Primrec.fst))
  have hkNW : Primrec fun q : Q => q.2.1 * (nonemptyExtWords (ctxI q.1) (ctxD q.1)).length :=
    Primrec.nat_mul.comp hk hNW
  have hrs : Primrec fun q : Q => wordsOf (List.range q.2.1) q.2.1 :=
    wordsOf_primrec.comp (Primrec.list_range.comp hk) hk
  have ho1s : Primrec fun q : Q × List ℕ =>
      wordsOf (List.range ((ctxI q.1.1).m1 + 1))
        (q.1.2.1 * (nonemptyExtWords (ctxI q.1.1) (ctxD q.1.1)).length) :=
    wordsOf_primrec.comp
      (Primrec.list_range.comp
        (Primrec.succ.comp (primrec_instM1.comp (primrec_ctxI.comp (Primrec.fst.comp Primrec.fst)))))
      (hkNW.comp Primrec.fst)
  have ho2s : Primrec fun q : (Q × List ℕ) × List ℕ =>
      wordsOf (List.range ((ctxI q.1.1.1).m2 + 1))
        (q.1.1.2.1 * (nonemptyExtWords (ctxI q.1.1.1) (ctxD q.1.1.1)).length) :=
    wordsOf_primrec.comp
      (Primrec.list_range.comp
        (Primrec.succ.comp (primrec_instM2.comp (primrec_ctxI.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))))
      (hkNW.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.list_flatMap hrs
    (Primrec.list_flatMap ho1s
      (Primrec.list_map ho2s
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂).to₂

lemma primrec₂_fixedIdxs : Primrec₂ fixedIdxs :=
  filter_primrec (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.ite
      (Primrec.eq.comp
        ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        Primrec.snd)
      (Primrec.const true) (Primrec.const false))

lemma primrec_decodeOr {α : Type} [Primcodable α] (d : α) : Primrec (decodeOr d) :=
  (Primrec.option_casesOn Primrec.decode (Primrec.const d) Primrec.snd.to₂).of_eq fun n => by
    unfold decodeOr; cases Encodable.decode (α := α) n <;> rfl

lemma decodeOr_encode {α : Type} [Primcodable α] (d a : α) :
    decodeOr d (Encodable.encode a) = a := by
  simp [decodeOr]

lemma unpackCtx_packCtx (c : SymCtx) : unpackCtx (packCtx c) = c := by
  rcases c with ⟨I, Dm1, b, lv⟩
  simp [packCtx, unpackCtx, decodeOr_encode]

lemma primrec_packCtx : Primrec packCtx := by
  have h1 : Primrec fun c : SymCtx => Encodable.encode c.1 :=
    Primrec.encode.comp primrec_ctxI
  have h2 : Primrec fun c : SymCtx => c.2.1 :=
    Primrec.fst.comp Primrec.snd
  have h3 : Primrec fun c : SymCtx => Encodable.encode c.2.2.1 :=
    Primrec.encode.comp primrec_ctxBCode
  have h4 : Primrec fun c : SymCtx => Encodable.encode c.2.2.2 :=
    Primrec.encode.comp primrec_ctxLive
  exact primrec₂_natPair.comp h1 (primrec₂_natPair.comp h2 (primrec₂_natPair.comp h3 h4))

lemma primrec_unpackCtx : Primrec unpackCtx := by
  have u1 : Primrec fun n : ℕ => n.unpair := Primrec.unpair
  have u2 : Primrec fun n : ℕ => n.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u1)
  have u3 : Primrec fun n : ℕ => n.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u2)
  exact ((primrec_decodeOr inhInstance).comp (Primrec.fst.comp u1)).pair
    ((Primrec.fst.comp u2).pair
      (((primrec_decodeOr ((0, [], []) : GenDPACode)).comp (Primrec.fst.comp u3)).pair
        ((primrec_decodeOr ([] : List Bool)).comp (Primrec.snd.comp u3))))

lemma primrec_decide_eq {α β : Type} [Primcodable α] [Primcodable β] [DecidableEq β]
    {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a = g a) :=
  (Primrec.ite (Primrec.eq.comp hf hg) (Primrec.const true) (Primrec.const false)).of_eq
    fun a => by by_cases h : f a = g a <;> simp [h]

lemma primrec_decide_le {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => decide (f a ≤ g a) :=
  (Primrec.ite (Primrec.nat_le.comp hf hg) (Primrec.const true) (Primrec.const false)).of_eq
    fun a => by by_cases h : f a ≤ g a <;> simp [h]

def impBool (a b : Bool) : Bool :=
  match a with
  | false => true
  | true => b

lemma primrec₂_impBool : Primrec₂ impBool :=
  (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const false))
    (Primrec.const true) Primrec.snd).of_eq fun ⟨a, b⟩ => by cases a <;> rfl

@[simp] lemma impBool_eq (a b : Bool) : impBool a b = (!a || b) := by
  cases a <;> rfl

def allListBool (l : List ℕ) (f : ℕ → Bool) : Bool :=
  l.foldl (fun acc x => andBool acc (f x)) true

lemma allListBool_eq_true (l : List ℕ) (f : ℕ → Bool) :
    allListBool l f = true ↔ ∀ x ∈ l, f x = true := by
  suffices ∀ b : Bool,
      l.foldl (fun acc x => andBool acc (f x)) b = true ↔ b = true ∧ ∀ x ∈ l, f x = true by
    simpa [allListBool] using this true
  induction l with
  | nil => intro b; simp
  | cons x xs ih =>
    intro b
    rw [List.foldl_cons, ih]
    simp only [andBool_eq, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, and_assoc]

lemma primrec_allListBool {α : Type} [Primcodable α] {l : α → List ℕ} {f : α × ℕ → Bool}
    (hl : Primrec l) (hf : Primrec f) :
    Primrec fun a => allListBool (l a) (fun x => f (a, x)) :=
  Primrec.list_foldl hl (Primrec.const true)
    (primrec₂_andBool.comp (Primrec.fst.comp Primrec.snd)
      (hf.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))).to₂

lemma primrec_extEqNatAux
    (IOf : ℕ → Instance) (posOf : ℕ → SymPosCode)
    (iOf : ℕ → ℕ) (w1Of : ℕ → List ℕ) (jOf : ℕ → ℕ) (w2Of : ℕ → List ℕ)
    (hI : Primrec IOf) (hpos : Primrec posOf)
    (hi : Primrec iOf) (hw1 : Primrec w1Of) (hj : Primrec jOf) (hw2 : Primrec w2Of) :
    Primrec fun q : ℕ => extEqNat (IOf q) (posOf q) (iOf q) (w1Of q) (jOf q) (w2Of q) := by
  have he1 := primrec_eq1At.comp (hpos.pair (hi.pair hj))
  have he2 := primrec_eq2At.comp (hpos.pair (hi.pair hj))
  exact (primrec_extEqFrom.comp ((hI.pair (he1.pair he2)).pair (hw1.pair hw2))).of_eq fun _ => rfl

def extEqNatPacked (q : ℕ) : Bool × Bool :=
  extEqNat
    (decodeOr inhInstance q.unpair.1)
    (decodeOr initSymPos q.unpair.2.unpair.1)
    q.unpair.2.unpair.2.unpair.1
    (decodeOr ([] : List ℕ) q.unpair.2.unpair.2.unpair.2.unpair.1)
    q.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1
    (decodeOr ([] : List ℕ) q.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2)

lemma primrec_extEqNatPacked : Primrec extEqNatPacked := by
  have u1 : Primrec fun q : ℕ => q.unpair := Primrec.unpair
  have u2 : Primrec fun q : ℕ => q.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u1)
  have u3 : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u2)
  have u4 : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u3)
  have u5 : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u4)
  exact primrec_extEqNatAux _ _ _ _ _ _
    ((primrec_decodeOr inhInstance).comp (Primrec.fst.comp u1))
    ((primrec_decodeOr initSymPos).comp (Primrec.fst.comp u2))
    (Primrec.fst.comp u3)
    ((primrec_decodeOr ([] : List ℕ)).comp (Primrec.fst.comp u4))
    (Primrec.fst.comp u5)
    ((primrec_decodeOr ([] : List ℕ)).comp (Primrec.snd.comp u5))

lemma primrec_extEqNatOf {α : Type} [Primcodable α]
    {I : α → Instance} {pos : α → SymPosCode}
    {i : α → ℕ} {w1 : α → List ℕ} {j : α → ℕ} {w2 : α → List ℕ}
    (hI : Primrec I) (hpos : Primrec pos)
    (hi : Primrec i) (hw1 : Primrec w1) (hj : Primrec j) (hw2 : Primrec w2) :
    Primrec fun a => extEqNat (I a) (pos a) (i a) (w1 a) (j a) (w2 a) := by
  have hp : Primrec fun a =>
      Nat.pair (Encodable.encode (I a))
        (Nat.pair (Encodable.encode (pos a))
          (Nat.pair (i a)
            (Nat.pair (Encodable.encode (w1 a))
              (Nat.pair (j a) (Encodable.encode (w2 a)))))) :=
    primrec₂_natPair.comp (Primrec.encode.comp hI)
      (primrec₂_natPair.comp (Primrec.encode.comp hpos)
        (primrec₂_natPair.comp hi
          (primrec₂_natPair.comp (Primrec.encode.comp hw1)
            (primrec₂_natPair.comp hj (Primrec.encode.comp hw2)))))
  exact (primrec_extEqNatPacked.comp hp).of_eq fun a => by
    simp only [extEqNatPacked, Nat.unpair_pair, decodeOr_encode]

def actValidExec (c : SymCtx) (pos : SymPosCode) (act : SymActCode) : Bool :=
  let k := pos.1
  let I := ctxI c
  let words := nonemptyExtWords I (ctxD c)
  let NW := words.length
  let fixed := fixedIdxs pos act
  let b1 := allListBool (List.range k) fun i =>
    decide (act.1.getD (act.1.getD i 0) 0 = act.1.getD i 0)
  let b2 := decide (fixed.length ≤ ctxBRed c)
  let b3 := allListBool (List.range k) fun i =>
    decide (stateAt pos (act.1.getD i 0) = stateAt pos i)
  let b4 := allListBool (List.range k) fun i =>
    allListBool (List.range k) fun j =>
      andBool
        (impBool (eq1At pos i j) (eq1At pos (act.1.getD i 0) (act.1.getD j 0)))
        (impBool (eq2At pos i j) (eq2At pos (act.1.getD i 0) (act.1.getD j 0)))
  let b5 := allListBool fixed fun i =>
    allListBool fixed fun j =>
      allListBool (List.range NW) fun wi =>
        allListBool (List.range NW) fun wj =>
          let eqs := extEqNat I pos i (words.getD wi []) j (words.getD wj [])
          andBool
            (impBool eqs.1 (decide (act.2.1.getD (i * NW + wi) 0 = act.2.1.getD (j * NW + wj) 0)))
            (impBool eqs.2 (decide (act.2.2.getD (i * NW + wi) 0 = act.2.2.getD (j * NW + wj) 0)))
  andBool b1 (andBool b2 (andBool b3 (andBool b4 b5)))

lemma actValidExec_eq_actValid (c : SymCtx) (pos : SymPosCode) (act : SymActCode) :
    actValidExec c pos act = actValid c pos act := by
  rw [Bool.eq_iff_iff]
  unfold actValid
  rw [decide_eq_true_eq]
  unfold actValidExec actValidProp
  simp only [andBool_eq, Bool.and_eq_true, allListBool_eq_true, List.mem_range,
    impBool_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  have h1 : ∀ b1 b2 : Bool, (b1 = false ∨ b2 = true) ↔ (b1 = true → b2 = true) := by
    intro b1 b2; cases b1 <;> cases b2 <;> decide
  have h2 : ∀ (b : Bool) (P : Prop), (b = false ∨ P) ↔ (b = true → P) := by
    intro b P; cases b <;> simp
  simp only [h1, h2]

lemma primrec_actValidExecAux
    (cOf : ℕ → SymCtx) (posOf : ℕ → SymPosCode) (actOf : ℕ → SymActCode)
    (hc : Primrec cOf) (hpos : Primrec posOf) (hact : Primrec actOf) :
    Primrec fun q : ℕ => actValidExec (cOf q) (posOf q) (actOf q) := by
  have hk : Primrec fun q : ℕ => (posOf q).1 := Primrec.fst.comp hpos
  have hrk : Primrec fun q : ℕ => List.range (posOf q).1 := Primrec.list_range.comp hk
  have hrL : Primrec fun q : ℕ => (actOf q).1 := Primrec.fst.comp hact
  have ho1 : Primrec fun q : ℕ => (actOf q).2.1 := Primrec.fst.comp (Primrec.snd.comp hact)
  have ho2 : Primrec fun q : ℕ => (actOf q).2.2 := Primrec.snd.comp (Primrec.snd.comp hact)
  have hwords : Primrec fun q : ℕ => nonemptyExtWords (ctxI (cOf q)) (ctxD (cOf q)) :=
    primrec₂_nonemptyExtWords.comp (primrec_ctxI.comp hc) (primrec_ctxD.comp hc)
  have hNW : Primrec fun q : ℕ => (nonemptyExtWords (ctxI (cOf q)) (ctxD (cOf q))).length :=
    Primrec.list_length.comp hwords
  have hrNW : Primrec fun q : ℕ => List.range (nonemptyExtWords (ctxI (cOf q)) (ctxD (cOf q))).length :=
    Primrec.list_range.comp hNW
  have hfix : Primrec fun q : ℕ => fixedIdxs (posOf q) (actOf q) := primrec₂_fixedIdxs.comp hpos hact
  -- 1. Idempotence
  have hb1 : Primrec fun q : ℕ => allListBool (List.range (posOf q).1) fun i =>
      decide ((actOf q).1.getD ((actOf q).1.getD i 0) 0 = (actOf q).1.getD i 0) := by
    have hri : Primrec fun p : ℕ × ℕ => (actOf p.1).1.getD p.2 0 :=
      (Primrec.list_getD 0).comp (hrL.comp Primrec.fst) Primrec.snd
    exact primrec_allListBool hrk
      (primrec_decide_eq ((Primrec.list_getD 0).comp (hrL.comp Primrec.fst) hri) hri)
  -- 2. Image bound
  have hb2 : Primrec fun q : ℕ => decide ((fixedIdxs (posOf q) (actOf q)).length ≤ ctxBRed (cOf q)) :=
    primrec_decide_le (Primrec.list_length.comp hfix) (primrec_ctxBRed.comp hc)
  -- 3. State preservation
  have hb3 : Primrec fun q : ℕ => allListBool (List.range (posOf q).1) fun i =>
      decide (stateAt (posOf q) ((actOf q).1.getD i 0) = stateAt (posOf q) i) := by
    have hri : Primrec fun p : ℕ × ℕ => (actOf p.1).1.getD p.2 0 :=
      (Primrec.list_getD 0).comp (hrL.comp Primrec.fst) Primrec.snd
    exact primrec_allListBool hrk
      (primrec_decide_eq (primrec₂_stateAt.comp (hpos.comp Primrec.fst) hri)
        (primrec₂_stateAt.comp (hpos.comp Primrec.fst) Primrec.snd))
  -- 4. View preservation
  have hb4 : Primrec fun q : ℕ => allListBool (List.range (posOf q).1) fun i =>
      allListBool (List.range (posOf q).1) fun j =>
        andBool
          (impBool (eq1At (posOf q) i j) (eq1At (posOf q) ((actOf q).1.getD i 0) ((actOf q).1.getD j 0)))
          (impBool (eq2At (posOf q) i j) (eq2At (posOf q) ((actOf q).1.getD i 0) ((actOf q).1.getD j 0))) := by
    let R4 := (ℕ × ℕ) × ℕ
    have r_pos : Primrec fun r : R4 => posOf r.1.1 := hpos.comp (Primrec.fst.comp Primrec.fst)
    have r_rL : Primrec fun r : R4 => (actOf r.1.1).1 := hrL.comp (Primrec.fst.comp Primrec.fst)
    have r_i : Primrec fun r : R4 => r.1.2 := Primrec.snd.comp Primrec.fst
    have r_j : Primrec fun r : R4 => r.2 := Primrec.snd
    have r_ri : Primrec fun r : R4 => (actOf r.1.1).1.getD r.1.2 0 := (Primrec.list_getD 0).comp r_rL r_i
    have r_rj : Primrec fun r : R4 => (actOf r.1.1).1.getD r.2 0 := (Primrec.list_getD 0).comp r_rL r_j
    have inner4 := primrec₂_andBool.comp
      (primrec₂_impBool.comp
        (primrec_eq1At.comp (r_pos.pair (r_i.pair r_j)))
        (primrec_eq1At.comp (r_pos.pair (r_ri.pair r_rj))))
      (primrec₂_impBool.comp
        (primrec_eq2At.comp (r_pos.pair (r_i.pair r_j)))
        (primrec_eq2At.comp (r_pos.pair (r_ri.pair r_rj))))
    exact primrec_allListBool hrk (primrec_allListBool (hrk.comp Primrec.fst) inner4)
  -- 5. Output coherence
  have hb5 : Primrec fun q : ℕ =>
      let I := ctxI (cOf q)
      let words := nonemptyExtWords I (ctxD (cOf q))
      let NW := words.length
      let fixed := fixedIdxs (posOf q) (actOf q)
      allListBool fixed fun i =>
        allListBool fixed fun j =>
          allListBool (List.range NW) fun wi =>
            allListBool (List.range NW) fun wj =>
              let eqs := extEqNat I (posOf q) i (words.getD wi []) j (words.getD wj [])
              andBool
                (impBool eqs.1 (decide ((actOf q).2.1.getD (i * NW + wi) 0 = (actOf q).2.1.getD (j * NW + wj) 0)))
                (impBool eqs.2 (decide ((actOf q).2.2.getD (i * NW + wi) 0 = (actOf q).2.2.getD (j * NW + wj) 0))) := by
    let R5 := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ
    have r_q : Primrec fun r : R5 => r.1.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have r_i : Primrec fun r : R5 => r.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have r_j : Primrec fun r : R5 => r.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have r_wi : Primrec fun r : R5 => r.1.2 := Primrec.snd.comp Primrec.fst
    have r_wj : Primrec fun r : R5 => r.2 := Primrec.snd
    have r_I := (primrec_ctxI.comp hc).comp r_q
    have r_pos := hpos.comp r_q
    have r_words := hwords.comp r_q
    have r_NW := hNW.comp r_q
    have r_w := (Primrec.list_getD ([] : List ℕ)).comp r_words r_wi
    have r_w' := (Primrec.list_getD ([] : List ℕ)).comp r_words r_wj
    have r_ext := primrec_extEqNatOf r_I r_pos r_i r_w r_j r_w'
    have r_idx1 := Primrec.nat_add.comp (Primrec.nat_mul.comp r_i r_NW) r_wi
    have r_idx2 := Primrec.nat_add.comp (Primrec.nat_mul.comp r_j r_NW) r_wj
    have inner5 := primrec₂_andBool.comp
      (primrec₂_impBool.comp (Primrec.fst.comp r_ext)
        (primrec_decide_eq
          ((Primrec.list_getD 0).comp (ho1.comp r_q) r_idx1)
          ((Primrec.list_getD 0).comp (ho1.comp r_q) r_idx2)))
      (primrec₂_impBool.comp (Primrec.snd.comp r_ext)
        (primrec_decide_eq
          ((Primrec.list_getD 0).comp (ho2.comp r_q) r_idx1)
          ((Primrec.list_getD 0).comp (ho2.comp r_q) r_idx2)))
    exact primrec_allListBool hfix
      (primrec_allListBool (hfix.comp Primrec.fst)
        (primrec_allListBool (hrNW.comp (Primrec.fst.comp Primrec.fst))
          (primrec_allListBool (hrNW.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) inner5)))
  exact (primrec₂_andBool.comp hb1
    (primrec₂_andBool.comp hb2
      (primrec₂_andBool.comp hb3
        (primrec₂_andBool.comp hb4 hb5)))).of_eq fun _ => rfl

lemma primrec_actValidPacked :
    Primrec fun q : ℕ =>
      actValid (unpackCtx q.unpair.1)
        (decodeOr initSymPos q.unpair.2.unpair.1)
        (decodeOr (([], [], []) : SymActCode) q.unpair.2.unpair.2) := by
  have hExec := primrec_actValidExecAux _ _ _
    (primrec_unpackCtx.comp (Primrec.fst.comp Primrec.unpair))
    ((primrec_decodeOr initSymPos).comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    ((primrec_decodeOr (([], [], []) : SymActCode)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  exact hExec.of_eq fun _ => actValidExec_eq_actValid _ _ _

lemma primrec_validActsForPacked :
    Primrec fun cp : ℕ => validActsFor (unpackCtx cp.unpair.1) (decodeOr initSymPos cp.unpair.2) := by
  have hc : Primrec fun cp : ℕ => unpackCtx cp.unpair.1 :=
    primrec_unpackCtx.comp (Primrec.fst.comp Primrec.unpair)
  have hpos : Primrec fun cp : ℕ => decodeOr initSymPos cp.unpair.2 :=
    (primrec_decodeOr initSymPos).comp (Primrec.snd.comp Primrec.unpair)
  have hallActs : Primrec fun cp : ℕ =>
      allSymActsFor (unpackCtx cp.unpair.1) (decodeOr initSymPos cp.unpair.2) :=
    primrec₂_allSymActsFor.comp hc hpos
  have hpred : Primrec fun p : ℕ × SymActCode =>
      actValid (unpackCtx p.1.unpair.1) (decodeOr initSymPos p.1.unpair.2) p.2 := by
    have hpack : Primrec fun p : ℕ × SymActCode =>
        Nat.pair p.1.unpair.1 (Nat.pair p.1.unpair.2 (Encodable.encode p.2)) :=
      primrec₂_natPair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
        (primrec₂_natPair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
          (Primrec.encode.comp Primrec.snd))
    exact (primrec_actValidPacked.comp hpack).of_eq fun p => by simp [decodeOr_encode]
  exact Primrec.list_map (filter_primrec hallActs hpred)
    ((hpos.comp Primrec.fst).pair Primrec.snd).to₂

lemma primrec_validSymLabels : Primrec validSymLabels := by
  have hPacked : Primrec fun cn : ℕ => validSymLabels (unpackCtx cn) := by
    have hallPos : Primrec fun cn : ℕ => allSymPos (unpackCtx cn) :=
      primrec_allSymPos.comp primrec_unpackCtx
    have hacts : Primrec fun p : ℕ × SymPosCode => validActsFor (unpackCtx p.1) p.2 := by
      have hcp : Primrec fun p : ℕ × SymPosCode => Nat.pair p.1 (Encodable.encode p.2) :=
        primrec₂_natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)
      exact (primrec_validActsForPacked.comp hcp).of_eq fun p => by simp [decodeOr_encode]
    exact dedupList_primrec.comp (Primrec.list_flatMap hallPos hacts.to₂)
  exact (hPacked.comp primrec_packCtx).of_eq fun c => by simp [unpackCtx_packCtx]

lemma nodup_validSymLabels (c : SymCtx) : (validSymLabels c).Nodup :=
  nodup_dedupList _

lemma mem_validSymLabels_iff (c : SymCtx) (pa : SymPosCode × SymActCode) :
    pa ∈ validSymLabels c ↔
      pa.1 ∈ allSymPos c ∧ pa.2 ∈ allSymActsFor c pa.1 ∧ actValid c pa.1 pa.2 = true := by
  rcases pa with ⟨pos, act⟩
  simp only [validSymLabels, validActsFor, mem_dedupList, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, hp, a, ⟨ha, hv⟩, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact ⟨hp, ha, hv⟩
  · rintro ⟨hp, ha, hv⟩
    exact ⟨pos, hp, act, ⟨ha, hv⟩, rfl⟩

lemma primrec_symNextStateAux (E : Thm34Engine)
    (cOf : ℕ → SymCtx) (posOf : ℕ → SymPosCode) (actOf : ℕ → SymActCode)
    (iOf : ℕ → ℕ) (uOf : ℕ → List ℕ)
    (hc : Primrec cOf) (hpos : Primrec posOf) (hact : Primrec actOf)
    (hi : Primrec iOf) (hu : Primrec uOf) :
    Primrec fun q : ℕ => symNextState E (cOf q) (posOf q) (actOf q) (iOf q) (uOf q) := by
  have hI := primrec_ctxI.comp hc
  have hD := primrec_ctxD.comp hc
  have hwords := primrec₂_nonemptyExtWords.comp hI hD
  have hNW := Primrec.list_length.comp hwords
  have hio : Primrec fun q : ℕ => (List.range (ctxD (cOf q))).map fun t =>
      let I := ctxI (cOf q)
      let words := nonemptyExtWords I (ctxD (cOf q))
      let NW := words.length
      let s := (uOf q).getD t 0
      let wi := cIdxOf words ((uOf q).take (t + 1))
      (decSigX1 I s, decSigX2 I s, decSigG s,
        (actOf q).2.1.getD (iOf q * NW + wi) 0,
        (actOf q).2.2.getD (iOf q * NW + wi) 0) := by
    let R := ℕ × ℕ
    have rq : Primrec fun r : R => r.1 := Primrec.fst
    have rt : Primrec fun r : R => r.2 := Primrec.snd
    have rs := (Primrec.list_getD 0).comp (hu.comp rq) rt
    have rtake := Primrec.list_take.comp (Primrec.succ.comp rt) (hu.comp rq)
    have rwi := primrec₂_cIdxOf.comp (hwords.comp rq) rtake
    have ridx := Primrec.nat_add.comp (Primrec.nat_mul.comp (hi.comp rq) (hNW.comp rq)) rwi
    have ry1 := (Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp (hact.comp rq))) ridx
    have ry2 := (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp (hact.comp rq))) ridx
    exact Primrec.list_map (Primrec.list_range.comp hD)
      ((primrec₂_decSigX1.comp (hI.comp rq) rs).pair
        ((primrec₂_decSigX2.comp (hI.comp rq) rs).pair
          ((primrec_decSigG.comp rs).pair (ry1.pair ry2)))).to₂
  have hA := Primrec.succ.comp (E.primrec_blockAlphaMinusOne.comp hI hD)
  have hbL := Primrec.nat_mod.comp (E.primrec_encIOBlockNat.comp ((hI.pair hD).pair hio)) hA
  have hbC := primrec_ctxBCode.comp hc
  have hst := primrec₂_stateAt.comp hpos hi
  exact (Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp hbC))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hst hA) hbL))
    (Primrec.succ.comp (Primrec.fst.comp hbC))).of_eq fun _ => rfl

lemma primrec_symNextStatePacked (E : Thm34Engine) : Primrec (symNextStatePacked E) := by
  have u1 : Primrec fun q : ℕ => q.unpair := Primrec.unpair
  have u2 : Primrec fun q : ℕ => q.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u1)
  have u3 : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u2)
  have u4 : Primrec fun q : ℕ => q.unpair.2.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u3)
  exact primrec_symNextStateAux E _ _ _ _ _
    (primrec_unpackCtx.comp (Primrec.fst.comp u1))
    ((primrec_decodeOr initSymPos).comp (Primrec.fst.comp u2))
    ((primrec_decodeOr (([], [], []) : SymActCode)).comp (Primrec.fst.comp u3))
    (Primrec.fst.comp u4)
    ((primrec_decodeOr ([] : List ℕ)).comp (Primrec.snd.comp u4))

lemma primrec_symNextStateOf {α : Type} [Primcodable α] (E : Thm34Engine)
    {c : α → SymCtx} {pos : α → SymPosCode} {act : α → SymActCode}
    {i : α → ℕ} {u : α → List ℕ}
    (hc : Primrec c) (hpos : Primrec pos) (hact : Primrec act)
    (hi : Primrec i) (hu : Primrec u) :
    Primrec fun a => symNextState E (c a) (pos a) (act a) (i a) (u a) := by
  have hp : Primrec fun a =>
      Nat.pair (packCtx (c a))
        (Nat.pair (Encodable.encode (pos a))
          (Nat.pair (Encodable.encode (act a))
            (Nat.pair (i a) (Encodable.encode (u a))))) :=
    primrec₂_natPair.comp (primrec_packCtx.comp hc)
      (primrec₂_natPair.comp (Primrec.encode.comp hpos)
        (primrec₂_natPair.comp (Primrec.encode.comp hact)
          (primrec₂_natPair.comp hi (Primrec.encode.comp hu))))
  exact ((primrec_symNextStatePacked E).comp hp).of_eq fun a => by
    simp only [symNextStatePacked, Nat.unpair_pair,
      unpackCtx_packCtx, decodeOr_encode]

lemma primrec_symLiveExtsAux (E : Thm34Engine)
    (cOf : ℕ → SymCtx) (posOf : ℕ → SymPosCode) (actOf : ℕ → SymActCode)
    (hc : Primrec cOf) (hpos : Primrec posOf) (hact : Primrec actOf) :
    Primrec fun q : ℕ => symLiveExts E (cOf q) (posOf q) (actOf q) := by
  have hfix : Primrec fun q : ℕ => fixedIdxs (posOf q) (actOf q) :=
    primrec₂_fixedIdxs.comp hpos hact
  have hblks : Primrec fun q : ℕ × ℕ => fullBlocks (ctxI (cOf q.1)) (ctxD (cOf q.1)) :=
    primrec₂_fullBlocks.comp
      (primrec_ctxI.comp (hc.comp Primrec.fst))
      (primrec_ctxD.comp (hc.comp Primrec.fst))
  let R := (ℕ × ℕ) × List ℕ
  have rq : Primrec fun r : R => r.1.1 := Primrec.fst.comp Primrec.fst
  have ri : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
  have ru : Primrec fun r : R => r.2 := Primrec.snd
  have rq' := primrec_symNextStateOf E (hc.comp rq) (hpos.comp rq) (hact.comp rq) ri ru
  have hlive := (Primrec.list_getD false).comp (primrec_ctxLive.comp (hc.comp rq)) rq'
  exact Primrec.list_flatMap hfix
    (Primrec.list_flatMap hblks
      (Primrec.ite (Primrec.eq.comp hlive (Primrec.const true))
        (Primrec.list_cons.comp (ri.pair (ru.pair rq')) (Primrec.const []))
        (Primrec.const [])).to₂).to₂

lemma primrec_symExtAdjOf {α : Type} [Primcodable α]
    {I : α → Instance} {pos : α → SymPosCode} {e1 e2 : α → SymExtElem}
    (hI : Primrec I) (hpos : Primrec pos) (he1 : Primrec e1) (he2 : Primrec e2) :
    Primrec fun a => symExtAdj (I a) (pos a) (e1 a) (e2 a) := by
  have heqs := primrec_extEqNatOf hI hpos
    (Primrec.fst.comp he1) (Primrec.fst.comp (Primrec.snd.comp he1))
    (Primrec.fst.comp he2) (Primrec.fst.comp (Primrec.snd.comp he2))
  exact (primrec₂_orBool.comp (Primrec.fst.comp heqs) (Primrec.snd.comp heqs)).of_eq fun _ => rfl

lemma primrec_symComponentsAux (E : Thm34Engine)
    (cOf : ℕ → SymCtx) (posOf : ℕ → SymPosCode) (actOf : ℕ → SymActCode)
    (hc : Primrec cOf) (hpos : Primrec posOf) (hact : Primrec actOf) :
    Primrec fun q : ℕ => symComponents E (cOf q) (posOf q) (actOf q) := by
  have hS := primrec_symLiveExtsAux E cOf posOf actOf hc hpos hact
  have hn : Primrec fun q : ℕ => (symLiveExts E (cOf q) (posOf q) (actOf q)).length :=
    Primrec.list_length.comp hS
  have hmat : Primrec fun q : ℕ =>
      let S := symLiveExts E (cOf q) (posOf q) (actOf q)
      (List.range S.length).flatMap fun a =>
        (List.range S.length).map fun b =>
          symExtAdj (ctxI (cOf q)) (posOf q) (S.getD a inhSymExt) (S.getD b inhSymExt) := by
    let R := (ℕ × ℕ) × ℕ
    have rq : Primrec fun r : R => r.1.1 := Primrec.fst.comp Primrec.fst
    have ra : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
    have rb : Primrec fun r : R => r.2 := Primrec.snd
    have rS := hS.comp rq
    have rcell := primrec_symExtAdjOf
      (primrec_ctxI.comp (hc.comp rq))
      (hpos.comp rq)
      ((Primrec.list_getD inhSymExt).comp rS ra)
      ((Primrec.list_getD inhSymExt).comp rS rb)
    exact Primrec.list_flatMap (Primrec.list_range.comp hn)
      (Primrec.list_map (Primrec.list_range.comp (hn.comp Primrec.fst)) rcell.to₂).to₂
  have hcomps : Primrec fun q : ℕ =>
      componentsIdx inhSymExt (symLiveExts E (cOf q) (posOf q) (actOf q))
        (symExtAdj (ctxI (cOf q)) (posOf q)) :=
    (primrec₂_componentsIdxMat.comp hn hmat).of_eq fun _ =>
      (componentsIdx_eq_mat inhSymExt _ _).symm
  exact (Primrec.list_map hcomps
    (Primrec.list_map Primrec.snd
      ((Primrec.list_getD inhSymExt).comp
        (hS.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂).of_eq fun _ => rfl

lemma primrec_symComponentsPacked (E : Thm34Engine) : Primrec (symComponentsPacked E) := by
  have u1 : Primrec fun q : ℕ => q.unpair := Primrec.unpair
  have u2 : Primrec fun q : ℕ => q.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u1)
  exact primrec_symComponentsAux E _ _ _
    (primrec_unpackCtx.comp (Primrec.fst.comp u1))
    ((primrec_decodeOr initSymPos).comp (Primrec.fst.comp u2))
    ((primrec_decodeOr (([], [], []) : SymActCode)).comp (Primrec.snd.comp u2))

lemma primrec_symComponentsOf {α : Type} [Primcodable α] (E : Thm34Engine)
    {c : α → SymCtx} {pos : α → SymPosCode} {act : α → SymActCode}
    (hc : Primrec c) (hpos : Primrec pos) (hact : Primrec act) :
    Primrec fun a => symComponents E (c a) (pos a) (act a) := by
  have hp : Primrec fun a =>
      Nat.pair (packCtx (c a))
        (Nat.pair (Encodable.encode (pos a)) (Encodable.encode (act a))) :=
    primrec₂_natPair.comp (primrec_packCtx.comp hc)
      (primrec₂_natPair.comp (Primrec.encode.comp hpos) (Primrec.encode.comp hact))
  exact ((primrec_symComponentsPacked E).comp hp).of_eq fun a => by
    simp only [symComponentsPacked, Nat.unpair_pair,
      unpackCtx_packCtx, decodeOr_encode]

lemma primrec_childSymPosAux
    (IOf : ℕ → Instance) (posOf : ℕ → SymPosCode) (compOf : ℕ → List SymExtElem)
    (hI : Primrec IOf) (hpos : Primrec posOf) (hcomp : Primrec compOf) :
    Primrec fun q : ℕ => childSymPos (IOf q) (posOf q) (compOf q) := by
  have hk' : Primrec fun q : ℕ => (compOf q).length := Primrec.list_length.comp hcomp
  let R := (ℕ × ℕ) × ℕ
  have rq : Primrec fun r : R => r.1.1 := Primrec.fst.comp Primrec.fst
  have ra : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
  have rb : Primrec fun r : R => r.2 := Primrec.snd
  have rea := (Primrec.list_getD inhSymExt).comp (hcomp.comp rq) ra
  have reb := (Primrec.list_getD inhSymExt).comp (hcomp.comp rq) rb
  have rext := primrec_extEqNatOf
    (hI.comp rq) (hpos.comp rq)
    (Primrec.fst.comp rea) (Primrec.fst.comp (Primrec.snd.comp rea))
    (Primrec.fst.comp reb) (Primrec.fst.comp (Primrec.snd.comp reb))
  have heq1' : Primrec _ := Primrec.list_flatMap (Primrec.list_range.comp hk')
    (Primrec.list_map (Primrec.list_range.comp (hk'.comp Primrec.fst)) (Primrec.fst.comp rext).to₂).to₂
  have heq2' : Primrec _ := Primrec.list_flatMap (Primrec.list_range.comp hk')
    (Primrec.list_map (Primrec.list_range.comp (hk'.comp Primrec.fst)) (Primrec.snd.comp rext).to₂).to₂
  have hst' : Primrec fun q : ℕ => (compOf q).map fun e => e.2.2 :=
    Primrec.list_map hcomp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂
  exact (hk'.pair (heq1'.pair (heq2'.pair hst'))).of_eq fun _ => rfl

def childSymPosPacked (q : ℕ) : SymPosCode :=
  childSymPos
    (decodeOr inhInstance q.unpair.1)
    (decodeOr initSymPos q.unpair.2.unpair.1)
    (decodeOr ([] : List SymExtElem) q.unpair.2.unpair.2)

lemma primrec_childSymPosPacked : Primrec childSymPosPacked := by
  have u1 : Primrec fun q : ℕ => q.unpair := Primrec.unpair
  have u2 : Primrec fun q : ℕ => q.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u1)
  exact primrec_childSymPosAux _ _ _
    ((primrec_decodeOr inhInstance).comp (Primrec.fst.comp u1))
    ((primrec_decodeOr initSymPos).comp (Primrec.fst.comp u2))
    ((primrec_decodeOr ([] : List SymExtElem)).comp (Primrec.snd.comp u2))

lemma primrec_childSymPosOf {α : Type} [Primcodable α]
    {I : α → Instance} {pos : α → SymPosCode} {comp : α → List SymExtElem}
    (hI : Primrec I) (hpos : Primrec pos) (hcomp : Primrec comp) :
    Primrec fun a => childSymPos (I a) (pos a) (comp a) := by
  have hp : Primrec fun a =>
      Nat.pair (Encodable.encode (I a))
        (Nat.pair (Encodable.encode (pos a)) (Encodable.encode (comp a))) :=
    primrec₂_natPair.comp (Primrec.encode.comp hI)
      (primrec₂_natPair.comp (Primrec.encode.comp hpos) (Primrec.encode.comp hcomp))
  exact (primrec_childSymPosPacked.comp hp).of_eq fun a => by
    simp only [childSymPosPacked, Nat.unpair_pair, decodeOr_encode]

lemma primrec_edgeStepOkOf {α : Type} [Primcodable α] (E : Thm34Engine)
    {c : α → SymCtx} {lbls : α → List (SymPosCode × SymActCode)}
    {a d i p j : α → ℕ}
    (hc : Primrec c) (hlbls : Primrec lbls)
    (ha : Primrec a) (hd : Primrec d) (hi : Primrec i) (hp : Primrec p) (hj : Primrec j) :
    Primrec fun x => edgeStepOk E (c x) (lbls x) (a x) (d x) (i x) (p x) (j x) := by
  have hpa := (Primrec.list_getD (initSymPos, ([], [], []))).comp hlbls
    (Primrec.nat_sub.comp ha (Primrec.const 1))
  have hpos := Primrec.fst.comp hpa
  have hact := Primrec.snd.comp hpa
  have hcomps := primrec_symComponentsOf E hc hpos hact
  have hcomp := (Primrec.list_getD ([] : List SymExtElem)).comp hcomps hd
  have hej := (Primrec.list_getD (0, [], 0)).comp hcomp hj
  have hcheck := primrec₂_andBool.comp
    (primrec_decide_eq (Primrec.fst.comp hej)
      ((Primrec.list_getD 0).comp (Primrec.fst.comp hact) hi))
    (primrec_decide_eq hp
      ((Primrec.list_getD 0).comp
        (Primrec.snd.comp (Primrec.snd.comp (primrec_ctxBCode.comp hc)))
        (Primrec.snd.comp (Primrec.snd.comp hej))))
  exact (Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) (Primrec.const false)
    (Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp ha (Primrec.const 1)) (Primrec.list_length.comp hlbls))
      (Primrec.ite (Primrec.nat_lt.comp hd (Primrec.list_length.comp hcomps))
        (Primrec.ite ((Primrec.nat_lt.comp hi (Primrec.fst.comp hpos)).and
            (Primrec.nat_lt.comp hj (Primrec.list_length.comp hcomp)))
          hcheck (Primrec.const false))
        (Primrec.const false))
      (Primrec.const false))).of_eq fun _ => rfl

lemma primrec_badThreadNBWNat (E : Thm34Engine)
    (cOf : ℕ → SymCtx) (lblsOf : ℕ → List (SymPosCode × SymActCode))
    (hc : Primrec cOf) (hlbls : Primrec lblsOf) :
    Primrec fun q : ℕ => badThreadNBW E (cOf q) (lblsOf q) := by
  have hB : Primrec fun q : ℕ => ctxBFull (cOf q) := primrec_ctxBFull.comp hc
  have hL : Primrec fun q : ℕ => (lblsOf q).length + 1 := Primrec.succ.comp (Primrec.list_length.comp hlbls)
  have hA : Primrec fun q : ℕ => ((lblsOf q).length + 1) * ctxBFull (cOf q) := Primrec.nat_mul.comp hL hB
  have hP : Primrec fun q : ℕ => maxList (ctxBCode (cOf q)).2.2 + 1 :=
    Primrec.succ.comp (primrec_maxList.comp
      (Primrec.snd.comp (Primrec.snd.comp (primrec_ctxBCode.comp hc))))
  have hS : Primrec fun q : ℕ => ctxBFull (cOf q) + ctxBFull (cOf q) * (maxList (ctxBCode (cOf q)).2.2 + 1) * 2 :=
    Primrec.nat_add.comp hB (Primrec.nat_mul.comp (Primrec.nat_mul.comp hB hP) (Primrec.const 2))
  -- accList
  have hacc : Primrec fun q : ℕ =>
      (List.range (ctxBFull (cOf q))).flatMap fun i =>
        (List.range (maxList (ctxBCode (cOf q)).2.2 + 1)).flatMap fun p_odd =>
          if p_odd % 2 = 1 then
            [ctxBFull (cOf q) + (i * (maxList (ctxBCode (cOf q)).2.2 + 1) + p_odd) * 2 + 1]
          else [] := by
    let R := (ℕ × ℕ) × ℕ
    have rq : Primrec fun r : R => r.1.1 := Primrec.fst.comp Primrec.fst
    have ri : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
    have rpo : Primrec fun r : R => r.2 := Primrec.snd
    have rtgt := Primrec.succ.comp (Primrec.nat_add.comp (hB.comp rq)
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp ri (hP.comp rq)) rpo)
        (Primrec.const 2)))
    exact Primrec.list_flatMap (Primrec.list_range.comp hB)
      (Primrec.list_flatMap (Primrec.list_range.comp (hP.comp Primrec.fst))
        (Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp rpo (Primrec.const 2)) (Primrec.const 1))
          (Primrec.list_cons.comp rtgt (Primrec.const []))
          (Primrec.const [])).to₂).to₂
  -- transRows cell for `(q_ctx, st, letter)`
  let C := (ℕ × ℕ) × ℕ
  have cq : Primrec fun x : C => x.1.1 := Primrec.fst.comp Primrec.fst
  have cst : Primrec fun x : C => x.1.2 := Primrec.snd.comp Primrec.fst
  have clet : Primrec fun x : C => x.2 := Primrec.snd
  have ca := Primrec.nat_div.comp clet (hB.comp cq)
  have cd := Primrec.nat_mod.comp clet (hB.comp cq)
  -- Phase 0 branch
  have hph0 : Primrec fun x : C =>
      let B_full := ctxBFull (cOf x.1.1)
      let P_cnt := maxList (ctxBCode (cOf x.1.1)).2.2 + 1
      let a := x.2 / B_full
      let d := x.2 % B_full
      let i := x.1.2
      (List.range P_cnt).flatMap fun p =>
        (List.range B_full).flatMap fun j =>
          if edgeStepOk E (cOf x.1.1) (lblsOf x.1.1) a d i p j = true then
            j :: ((List.range P_cnt).flatMap fun p_odd =>
              if p_odd % 2 = 1 ∧ p_odd ≤ p then
                [B_full + (j * P_cnt + p_odd) * 2 + (if p = p_odd then 1 else 0)]
              else [])
          else [] := by
    let R0 := (C × ℕ) × ℕ
    have rx : Primrec fun r : R0 => r.1.1 := Primrec.fst.comp Primrec.fst
    have rp : Primrec fun r : R0 => r.1.2 := Primrec.snd.comp Primrec.fst
    have rj : Primrec fun r : R0 => r.2 := Primrec.snd
    have rok := primrec_edgeStepOkOf E
      (hc.comp (cq.comp rx)) (hlbls.comp (cq.comp rx))
      (ca.comp rx) (cd.comp rx) (cst.comp rx) rp rj
    let R0' := R0 × ℕ
    have r0 : Primrec fun r : R0' => r.1 := Primrec.fst
    have rpo : Primrec fun r : R0' => r.2 := Primrec.snd
    have rhit := Primrec.ite (Primrec.eq.comp (rp.comp r0) rpo) (Primrec.const 1) (Primrec.const 0)
    have rtgt := Primrec.nat_add.comp
      (Primrec.nat_add.comp (hB.comp (cq.comp (rx.comp r0)))
        (Primrec.nat_mul.comp
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (rj.comp r0) (hP.comp (cq.comp (rx.comp r0)))) rpo)
          (Primrec.const 2)))
      rhit
    have rjumps : Primrec fun r : R0 =>
        (List.range (maxList (ctxBCode (cOf r.1.1.1.1)).2.2 + 1)).flatMap fun p_odd =>
          if p_odd % 2 = 1 ∧ p_odd ≤ r.1.2 then
            [ctxBFull (cOf r.1.1.1.1) + (r.2 * (maxList (ctxBCode (cOf r.1.1.1.1)).2.2 + 1) + p_odd) * 2 +
              (if r.1.2 = p_odd then 1 else 0)]
          else [] :=
      Primrec.list_flatMap (Primrec.list_range.comp (hP.comp (cq.comp rx)))
        (Primrec.ite
          ((Primrec.eq.comp (Primrec.nat_mod.comp rpo (Primrec.const 2)) (Primrec.const 1)).and
            (Primrec.nat_le.comp rpo (rp.comp r0)))
          (Primrec.list_cons.comp rtgt (Primrec.const []))
          (Primrec.const [])).to₂
    exact Primrec.list_flatMap (Primrec.list_range.comp (hP.comp cq))
      (Primrec.list_flatMap (Primrec.list_range.comp (hB.comp (cq.comp Primrec.fst)))
        (Primrec.ite (Primrec.eq.comp rok (Primrec.const true))
          (Primrec.list_cons.comp rj rjumps)
          (Primrec.const [])).to₂).to₂
  -- Phase 1 branch
  have hph1 : Primrec fun x : C =>
      let B_full := ctxBFull (cOf x.1.1)
      let P_cnt := maxList (ctxBCode (cOf x.1.1)).2.2 + 1
      let a := x.2 / B_full
      let d := x.2 % B_full
      let ip := (x.1.2 - B_full) / 2
      let i := ip / P_cnt
      let p_odd := ip % P_cnt
      if p_odd % 2 = 1 then
        (List.range P_cnt).flatMap fun p =>
          (List.range B_full).flatMap fun j =>
            if edgeStepOk E (cOf x.1.1) (lblsOf x.1.1) a d i p j = true ∧ p_odd ≤ p then
              [B_full + (j * P_cnt + p_odd) * 2 + (if p = p_odd then 1 else 0)]
            else []
      else [] := by
    have hip := Primrec.nat_div.comp (Primrec.nat_sub.comp cst (hB.comp cq)) (Primrec.const 2)
    have hi1 := Primrec.nat_div.comp hip (hP.comp cq)
    have hpo1 := Primrec.nat_mod.comp hip (hP.comp cq)
    let R1 := (C × ℕ) × ℕ
    have rx : Primrec fun r : R1 => r.1.1 := Primrec.fst.comp Primrec.fst
    have rp : Primrec fun r : R1 => r.1.2 := Primrec.snd.comp Primrec.fst
    have rj : Primrec fun r : R1 => r.2 := Primrec.snd
    have rok := primrec_edgeStepOkOf E
      (hc.comp (cq.comp rx)) (hlbls.comp (cq.comp rx))
      (ca.comp rx) (cd.comp rx) (hi1.comp rx) rp rj
    have rhit := Primrec.ite (Primrec.eq.comp rp (hpo1.comp rx)) (Primrec.const 1) (Primrec.const 0)
    have rtgt := Primrec.nat_add.comp
      (Primrec.nat_add.comp (hB.comp (cq.comp rx))
        (Primrec.nat_mul.comp
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp rj (hP.comp (cq.comp rx))) (hpo1.comp rx))
          (Primrec.const 2)))
      rhit
    have rbody := Primrec.list_flatMap (Primrec.list_range.comp (hP.comp cq))
      (Primrec.list_flatMap (Primrec.list_range.comp (hB.comp (cq.comp Primrec.fst)))
        (Primrec.ite ((Primrec.eq.comp rok (Primrec.const true)).and
            (Primrec.nat_le.comp (hpo1.comp rx) rp))
          (Primrec.list_cons.comp rtgt (Primrec.const []))
          (Primrec.const [])).to₂).to₂
    exact Primrec.ite
      (Primrec.eq.comp (Primrec.nat_mod.comp hpo1 (Primrec.const 2)) (Primrec.const 1))
      rbody (Primrec.const [])
  have htrans : Primrec fun q : ℕ => (badThreadNBW E (cOf q) (lblsOf q)).2.2.1 :=
    Primrec.list_flatMap (Primrec.list_range.comp hS)
      (Primrec.list_map (Primrec.list_range.comp (hA.comp Primrec.fst))
        (Primrec.ite (Primrec.nat_lt.comp cst (hB.comp cq)) hph0 hph1).to₂).to₂
  exact ((Primrec.nat_sub.comp hS (Primrec.const 1)).pair
    ((Primrec.const [0]).pair (htrans.pair hacc))).of_eq fun _ => rfl

lemma badThreadNBW_accepts_iff (E : Thm34Engine) (c : SymCtx)
    (labels : List (SymPosCode × SymActCode))
    (ad : ℕ → Fin (labels.length + 1) × Fin (ctxBFull c)) :
    let B_full := ctxBFull c
    let L_sym := labels.length + 1
    let αMon := L_sym * B_full - 1
    let K_prio := maxList (ctxBCode c).2.2
    have hα_pos : 0 < L_sym * B_full := Nat.mul_pos (Nat.succ_pos _) (ctxBFull_pos c)
    let w : ℕ → Fin (αMon + 1) := fun n =>
      ⟨(ad n).1.val * B_full + (ad n).2.val, by
        rw [Nat.sub_add_cancel hα_pos]
        have h1 : (ad n).1.val + 1 ≤ L_sym := (ad n).1.isLt
        calc
          (ad n).1.val * B_full + (ad n).2.val < (ad n).1.val * B_full + B_full :=
            Nat.add_lt_add_left (ad n).2.isLt _
          _ = ((ad n).1.val + 1) * B_full := by ring
          _ ≤ L_sym * B_full := Nat.mul_le_mul_right B_full h1⟩
    ListNBWAccepts αMon (badThreadNBW E c labels) w ↔
      ∃ (iSeq : ℕ → Fin B_full) (pSeq : ℕ → Fin (K_prio + 1)),
        (iSeq 0).val = 0 ∧
        (∀ n, edgeStepOk E c labels (ad n).1.val (ad n).2.val
          (iSeq n).val (pSeq n).val (iSeq (n + 1)).val = true) ∧
        OddParityCond (fun n => (pSeq n).val) := by
  intro B_full L_sym αMon K_prio hα_pos w
  let P_cnt := K_prio + 1
  let S_nbw := B_full + B_full * P_cnt * 2
  have hB_pos : 0 < B_full := ctxBFull_pos c
  have hP_pos : 0 < P_cnt := Nat.succ_pos _
  have hS_pos : 0 < S_nbw := by positivity
  have hS_succ : (S_nbw - 1) + 1 = S_nbw := Nat.sub_add_cancel hS_pos
  have hA_succ : αMon + 1 = L_sym * B_full := Nat.sub_add_cancel hα_pos
  have hw_div_mod : ∀ n, (w n).val / B_full = (ad n).1.val ∧ (w n).val % B_full = (ad n).2.val := by
    intro n
    dsimp only [w]
    have hrew : (ad n).1.val * B_full + (ad n).2.val = (ad n).2.val + B_full * (ad n).1.val := by ring
    rw [hrew]
    exact ⟨by rw [Nat.add_mul_div_left _ _ hB_pos, Nat.div_eq_of_lt (ad n).2.isLt, zero_add],
      by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ad n).2.isLt]⟩
  have htrans_getD : ∀ (q : ℕ) (hq : q < S_nbw) (n : ℕ),
      (badThreadNBW E c labels).2.2.1.getD ((αMon + 1) * q + (w n).val) [] =
        let a := (ad n).1.val
        let d := (ad n).2.val
        if q < B_full then
          (List.range P_cnt).flatMap fun p =>
            (List.range B_full).flatMap fun j =>
              if edgeStepOk E c labels a d q p j = true then
                j :: ((List.range P_cnt).flatMap fun p_odd =>
                  if p_odd % 2 = 1 ∧ p_odd ≤ p then
                    [B_full + (j * P_cnt + p_odd) * 2 + (if p = p_odd then 1 else 0)]
                  else [])
              else []
        else
          let ip := (q - B_full) / 2
          let i := ip / P_cnt
          let p_odd := ip % P_cnt
          if p_odd % 2 = 1 then
            (List.range P_cnt).flatMap fun p =>
              (List.range B_full).flatMap fun j =>
                if edgeStepOk E c labels a d i p j = true ∧ p_odd ≤ p then
                  [B_full + (j * P_cnt + p_odd) * 2 + (if p = p_odd then 1 else 0)]
                else []
          else [] := by
    intro q hq n
    have hwl : (w n).val < L_sym * B_full := (w n).isLt.trans_eq hA_succ
    have hidx_lt : (L_sym * B_full) * q + (w n).val < S_nbw * (L_sym * B_full) := by
      have h1 : q + 1 ≤ S_nbw := hq
      calc
        (L_sym * B_full) * q + (w n).val < (L_sym * B_full) * q + L_sym * B_full :=
          Nat.add_lt_add_left hwl _
        _ = (q + 1) * (L_sym * B_full) := by ring
        _ ≤ S_nbw * (L_sym * B_full) := Nat.mul_le_mul_right _ h1
    -- Index into `flatMap` of fixed-size rows `L_sym * B_full`
    have hflat_idx : ∀ {α : Type} (R C_len : ℕ) (f : ℕ → ℕ → α) (r c0 : ℕ) (hr : r < R) (hc0 : c0 < C_len) (d0 : α),
        ((List.range R).flatMap fun x => (List.range C_len).map (f x)).getD (C_len * r + c0) d0 = f r c0 := by
      intro α R C_len f r c0 hr hc0 d0
      induction R with
      | zero => cases hr
      | succ R ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        have hlen_prefix : ((List.range R).flatMap fun x => (List.range C_len).map (f x)).length = C_len * R := by
          simp [List.length_flatMap, List.map_const', Nat.mul_comm]
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hr_lt
        · rw [getD_eq_getElem _ d0 (C_len * r + c0) (by simp [hlen_prefix]; omega),
            List.getElem_append_right (by omega)]
          simp [hlen_prefix]
        · have hlt_pre : C_len * r + c0 < C_len * R := by
            have h1 : r + 1 ≤ R := hr_lt
            calc
              C_len * r + c0 < C_len * r + C_len := Nat.add_lt_add_left hc0 _
              _ = C_len * (r + 1) := by ring
              _ ≤ C_len * R := Nat.mul_le_mul_left C_len h1
          rw [getD_eq_getElem _ d0 _ (by simp [hlen_prefix]; omega),
            List.getElem_append_left (by omega),
            ← getD_eq_getElem _ d0 _ (by omega)]
          exact ih hr_lt
    let wv := (w n).val
    change (badThreadNBW E c labels).2.2.1.getD ((αMon + 1) * q + wv) [] = _
    rw [hA_succ]
    dsimp only [badThreadNBW]
    rw [hflat_idx S_nbw (L_sym * B_full) _ q wv hq hwl [],
      (hw_div_mod n).1, (hw_div_mod n).2]
  rw [ListNBWAccepts_iff_frequently]
  constructor
  · rintro ⟨ρ, h0, hstep, hfreq⟩
    have hρ_lt : ∀ n, (ρ n).val < S_nbw := fun n => (ρ n).isLt.trans_eq hS_succ
    -- Extract edge index `iOf q < B_full`
    let iOf : ℕ → ℕ := fun q => if q < B_full then q else ((q - B_full) / 2) / P_cnt
    have hiOf_lt : ∀ n, iOf (ρ n).val < B_full := by
      intro n
      dsimp only [iOf]
      split_ifs with hlt
      · exact hlt
      · have hrem : (ρ n).val - B_full < B_full * P_cnt * 2 := by have := hρ_lt n; omega
        have hdiv2 : ((ρ n).val - B_full) / 2 < B_full * P_cnt :=
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr hrem
        exact (Nat.div_lt_iff_lt_mul hP_pos).mpr hdiv2
    let iSeq : ℕ → Fin B_full := fun n => ⟨iOf (ρ n).val, hiOf_lt n⟩
    have hi0 : (iSeq 0).val = 0 := by
      have h0' : (ρ 0).val = 0 := by simpa [badThreadNBW] using h0
      simp [iSeq, iOf, h0', hB_pos]
    -- Phase 1 states encode `(j, p_odd, hit)` cleanly
    have hph1_decode : ∀ (j p_odd hit : ℕ) (hj : j < B_full) (hpo : p_odd < P_cnt) (hhit : hit < 2),
        let q := B_full + (j * P_cnt + p_odd) * 2 + hit
        ¬ (q < B_full) ∧ ((q - B_full) / 2) / P_cnt = j ∧
          ((q - B_full) / 2) % P_cnt = p_odd ∧ (q - B_full) % 2 = hit := by
      intro j p_odd hit hj hpo hhit q
      have hsub : q - B_full = hit + 2 * (p_odd + P_cnt * j) := by
        have hmc : j * P_cnt = P_cnt * j := Nat.mul_comm _ _
        dsimp [q]; omega
      have hd2 : (q - B_full) / 2 = p_odd + P_cnt * j := by
        rw [hsub, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt hhit, zero_add]
      have hm2 : (q - B_full) % 2 = hit := by
        rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hhit]
      refine ⟨by dsimp [q]; omega, ?_, ?_, hm2⟩
      · rw [hd2, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hpo, zero_add]
      · rw [hd2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpo]
    -- At every step `n`, extract `p < P_cnt` with `edgeStepOk` + Phase 1 persistence
    have hstep_extract : ∀ n,
        ∃ p < P_cnt,
          edgeStepOk E c labels (ad n).1.val (ad n).2.val (iSeq n).val p (iSeq (n + 1)).val = true ∧
          (¬ ((ρ n).val < B_full) →
            let p_odd := (((ρ n).val - B_full) / 2) % P_cnt
            p_odd % 2 = 1 ∧ p_odd ≤ p ∧ ¬ ((ρ (n + 1)).val < B_full) ∧
              (((ρ (n + 1)).val - B_full) / 2) % P_cnt = p_odd ∧
              (((ρ (n + 1)).val - B_full) % 2 = 1 ↔ p = p_odd)) ∧
          (((ρ n).val < B_full) → ¬ ((ρ (n + 1)).val < B_full) →
            let p_odd := (((ρ (n + 1)).val - B_full) / 2) % P_cnt
            p_odd % 2 = 1 ∧ p_odd ≤ p ∧ (((ρ (n + 1)).val - B_full) % 2 = 1 ↔ p = p_odd)) := by
      intro n
      have hmem := hstep n
      rw [htrans_getD (ρ n).val (hρ_lt n) n] at hmem
      dsimp only at hmem
      by_cases hlt_n : (ρ n).val < B_full
      · rw [if_pos hlt_n] at hmem
        simp only [List.mem_flatMap, List.mem_range] at hmem
        rcases hmem with ⟨p, hp_lt, j, hj_lt, hmem2⟩
        by_cases hok : edgeStepOk E c labels (ad n).1.val (ad n).2.val (ρ n).val p j = true
        · rw [if_pos hok] at hmem2
          rcases List.mem_cons.mp hmem2 with hjeq | hjmp
          · have hij : (iSeq (n + 1)).val = j := by simp [iSeq, iOf, hjeq, hj_lt]
            have hin : (iSeq n).val = (ρ n).val := by simp [iSeq, iOf, hlt_n]
            refine ⟨p, hp_lt, by rwa [hin, hij], fun hn => False.elim (hn hlt_n),
              fun _ hn1 => False.elim (hn1 (hjeq ▸ hj_lt))⟩
          · simp only [List.mem_flatMap, List.mem_range] at hjmp
            rcases hjmp with ⟨p_odd, hpo_lt, hpo_mem⟩
            by_cases hpo_cond : p_odd % 2 = 1 ∧ p_odd ≤ p
            · rw [if_pos hpo_cond] at hpo_mem
              simp only [List.mem_singleton] at hpo_mem
              have hhit_lt : (if p = p_odd then 1 else 0) < 2 := by split_ifs <;> decide
              obtain ⟨hn_lt1, hij_c, hpo_c, hhit_c⟩ := hph1_decode j p_odd _ hj_lt hpo_lt hhit_lt
              rw [← hpo_mem] at hn_lt1 hij_c hpo_c hhit_c
              have hin : (iSeq n).val = (ρ n).val := by simp [iSeq, iOf, hlt_n]
              have hij : (iSeq (n + 1)).val = j := by simp [iSeq, iOf, hn_lt1, hij_c]
              refine ⟨p, hp_lt, by rwa [hin, hij], fun hn => False.elim (hn hlt_n), fun _ _ => ?_⟩
              dsimp only
              rw [hpo_c, hhit_c]
              exact ⟨hpo_cond.1, hpo_cond.2, by split_ifs with hpe <;> simp [hpe]⟩
            · rw [if_neg hpo_cond] at hpo_mem; simp at hpo_mem
        · rw [if_neg hok] at hmem2; simp at hmem2
      · rw [if_neg hlt_n] at hmem
        set p_odd := (((ρ n).val - B_full) / 2) % P_cnt
        by_cases hodd : p_odd % 2 = 1
        · rw [if_pos hodd] at hmem
          simp only [List.mem_flatMap, List.mem_range] at hmem
          rcases hmem with ⟨p, hp_lt, j, hj_lt, hmem2⟩
          by_cases hcond : edgeStepOk E c labels (ad n).1.val (ad n).2.val (((ρ n).val - B_full) / 2 / P_cnt) p j = true ∧ p_odd ≤ p
          · rw [if_pos hcond] at hmem2
            simp only [List.mem_singleton] at hmem2
            have hpo_lt : p_odd < P_cnt := Nat.mod_lt _ hP_pos
            have hhit_lt : (if p = p_odd then 1 else 0) < 2 := by split_ifs <;> decide
            obtain ⟨hn_lt1, hij_c, hpo_c, hhit_c⟩ := hph1_decode j p_odd _ hj_lt hpo_lt hhit_lt
            rw [← hmem2] at hn_lt1 hij_c hpo_c hhit_c
            have hin : (iSeq n).val = (((ρ n).val - B_full) / 2) / P_cnt := by simp [iSeq, iOf, hlt_n]
            have hij : (iSeq (n + 1)).val = j := by simp [iSeq, iOf, hn_lt1, hij_c]
            refine ⟨p, hp_lt, by rw [hin, hij]; exact hcond.1, fun _ => ?_, fun h => False.elim (hlt_n h)⟩
            dsimp only
            rw [hpo_c, hhit_c]
            exact ⟨hodd, hcond.2, hn_lt1, rfl, by split_ifs with hpe <;> simp [hpe]⟩
          · rw [if_neg hcond] at hmem2; simp at hmem2
        · rw [if_neg hodd] at hmem; simp at hmem
    classical
    let pSeq : ℕ → Fin P_cnt := fun n =>
      ⟨(hstep_extract n).choose, (hstep_extract n).choose_spec.1⟩
    have hp_ok : ∀ n, edgeStepOk E c labels (ad n).1.val (ad n).2.val
        (iSeq n).val (pSeq n).val (iSeq (n + 1)).val = true :=
      fun n => (hstep_extract n).choose_spec.2.1
    -- Every accepting state has `¬ (q < B_full)` and `(q - B_full) % 2 = 1`
    have hacc_char : ∀ q, q ∈ (badThreadNBW E c labels).2.2.2 →
        ¬ (q < B_full) ∧ (q - B_full) % 2 = 1 := by
      intro q hq
      simp only [badThreadNBW, List.mem_flatMap, List.mem_range] at hq
      rcases hq with ⟨i, hi_lt, po, hpo_lt, hq_mem⟩
      split_ifs at hq_mem with hpo_odd
      · simp only [List.mem_singleton] at hq_mem
        obtain ⟨hn_b, _, _, hm2⟩ := hph1_decode i po 1 hi_lt hpo_lt (by decide)
        rw [hq_mem]; exact ⟨hn_b, hm2⟩
      · simp at hq_mem
    -- Find first time `N + 1` in Phase 1 from `hfreq`
    obtain ⟨t_acc, ht_acc⟩ := hfreq.exists
    obtain ⟨hn_acc, _⟩ := hacc_char (ρ t_acc).val ht_acc
    have ht_pos : 1 ≤ t_acc := by
      by_contra h0_t
      have htz : t_acc = 0 := by omega
      subst htz
      have h0' : (ρ 0).val = 0 := by simpa [badThreadNBW] using h0
      exact hn_acc (by rw [h0']; exact hB_pos)
    -- Stay in Phase 1 with constant `p_odd` for all `t ≥ t_acc`
    let p_odd := (((ρ t_acc).val - B_full) / 2) % P_cnt
    have hlock : ∀ k, ¬ ((ρ (t_acc + k)).val < B_full) ∧
        (((ρ (t_acc + k)).val - B_full) / 2) % P_cnt = p_odd ∧
        p_odd % 2 = 1 ∧ p_odd ≤ (pSeq (t_acc + k)).val ∧
        (((ρ (t_acc + k + 1)).val - B_full) % 2 = 1 ↔ (pSeq (t_acc + k)).val = p_odd) := by
      intro k
      induction k with
      | zero =>
        simp only [Nat.add_zero]
        have hs := (hstep_extract t_acc).choose_spec.2.2.1 hn_acc
        exact ⟨hn_acc, rfl, hs.1, hs.2.1, hs.2.2.2.2⟩
      | succ k ih =>
        have heq_add : t_acc + (k + 1) = (t_acc + k) + 1 := by omega
        rw [heq_add]
        have hs1 := (hstep_extract (t_acc + k)).choose_spec.2.2.1 ih.1
        have hn1 : ¬ ((ρ (t_acc + k + 1)).val < B_full) := hs1.2.2.1
        have hpo1 : (((ρ (t_acc + k + 1)).val - B_full) / 2) % P_cnt = p_odd :=
          hs1.2.2.2.1.trans ih.2.1
        have hs2 := (hstep_extract (t_acc + k + 1)).choose_spec.2.2.1 hn1
        have hle2 : (((ρ (t_acc + k + 1)).val - B_full) / 2) % P_cnt ≤ (pSeq (t_acc + k + 1)).val :=
          hs2.2.1
        have hiff2 : (((ρ (t_acc + k + 1 + 1)).val - B_full) % 2 = 1) ↔
            (pSeq (t_acc + k + 1)).val = (((ρ (t_acc + k + 1)).val - B_full) / 2) % P_cnt :=
          hs2.2.2.2.2
        refine ⟨hn1, hpo1, ih.2.2.1, by omega, ?_⟩
        rw [hiff2, hpo1]
    refine ⟨iSeq, pSeq, hi0, hp_ok, p_odd, ?_, ?_, ?_⟩
    · exact ⟨p_odd / 2, by have := (hlock 0).2.2.1; omega⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro M
      obtain ⟨m, hm_ge, hm_acc⟩ := hfreq (max (M + 1) (t_acc + 1))
      have hm_gt_t : t_acc + 1 ≤ m := le_trans (le_max_right _ _) hm_ge
      let k := m - t_acc - 1
      have hm_eq : m = t_acc + k + 1 := by omega
      obtain ⟨_, hm_hit⟩ := hacc_char (ρ m).val hm_acc
      rw [hm_eq] at hm_hit
      have hp_eq := ((hlock k).2.2.2.2).mp hm_hit
      exact ⟨t_acc + k, by omega, hp_eq⟩
    · rw [Filter.eventually_atTop]
      refine ⟨t_acc, fun n hn => ?_⟩
      have hn_eq : n = t_acc + (n - t_acc) := by omega
      rw [hn_eq]
      exact (hlock (n - t_acc)).2.2.2.1
  · rintro ⟨iSeq, pSeq, hi0, hp_ok, p_odd, ⟨k_odd, rfl⟩, hfreq, hev⟩
    let p_val := 2 * k_odd + 1
    obtain ⟨t_ex, ht_ex⟩ := hfreq.exists
    have hpo_lt : p_val < P_cnt := by
      have := (pSeq t_ex).isLt
      dsimp only [p_val] at ht_ex ⊢
      omega
    have hpo_mod : p_val % 2 = 1 := by omega
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    let ρVal : ℕ → ℕ := fun n =>
      if n ≤ N then (iSeq n).val
      else B_full + ((iSeq n).val * P_cnt + p_val) * 2 +
        (if (pSeq (n - 1)).val = p_val then 1 else 0)
    have hρ_lt : ∀ n, ρVal n < S_nbw := by
      intro n
      dsimp only [ρVal]
      by_cases hn : n ≤ N
      · rw [if_pos hn]; have := (iSeq n).isLt; dsimp [S_nbw]; omega
      · rw [if_neg hn]
        have h1 : (iSeq n).val + 1 ≤ B_full := (iSeq n).isLt
        have hip : (iSeq n).val * P_cnt + p_val < B_full * P_cnt := by
          calc
            (iSeq n).val * P_cnt + p_val < (iSeq n).val * P_cnt + P_cnt :=
              Nat.add_lt_add_left hpo_lt _
            _ = ((iSeq n).val + 1) * P_cnt := by ring
            _ ≤ B_full * P_cnt := Nat.mul_le_mul_right P_cnt h1
        have h2 : (iSeq n).val * P_cnt + p_val + 1 ≤ B_full * P_cnt := hip
        have hmul2 : ((iSeq n).val * P_cnt + p_val) * 2 +
            (if (pSeq (n - 1)).val = p_val then 1 else 0) < B_full * P_cnt * 2 := by
          have hb : (if (pSeq (n - 1)).val = p_val then 1 else 0) < 2 := by split_ifs <;> decide
          calc
            _ < ((iSeq n).val * P_cnt + p_val) * 2 + 2 := Nat.add_lt_add_left hb _
            _ = ((iSeq n).val * P_cnt + p_val + 1) * 2 := by ring
            _ ≤ (B_full * P_cnt) * 2 := Nat.mul_le_mul_right 2 h2
        dsimp [S_nbw]; omega
    let ρ : ℕ → Fin ((badThreadNBW E c labels).1 + 1) :=
      fun n => ⟨ρVal n, hS_succ.symm ▸ hρ_lt n⟩
    refine ⟨ρ, by simp [ρ, ρVal, hi0, badThreadNBW], ?_, ?_⟩
    · intro n
      change ρVal (n + 1) ∈ (badThreadNBW E c labels).2.2.1.getD ((αMon + 1) * ρVal n + (w n).val) []
      rw [htrans_getD (ρVal n) (hρ_lt n) n]
      dsimp only
      by_cases hn_lt : n < N
      · -- Stay in Phase 0: `n ≤ N` and `n + 1 ≤ N`
        have hn_le : n ≤ N := Nat.le_of_lt hn_lt
        have hn1_le : n + 1 ≤ N := hn_lt
        have hρn : ρVal n = (iSeq n).val := if_pos hn_le
        have hρn1 : ρVal (n + 1) = (iSeq (n + 1)).val := if_pos hn1_le
        rw [hρn, hρn1, if_pos (iSeq n).isLt]
        simp only [List.mem_flatMap, List.mem_range]
        refine ⟨(pSeq n).val, (pSeq n).isLt, (iSeq (n + 1)).val, (iSeq (n + 1)).isLt, ?_⟩
        rw [if_pos (hp_ok n)]
        exact List.mem_cons.mpr (Or.inl rfl)
      · by_cases hn_eq : n = N
        · -- Jump from Phase 0 to Phase 1 at `n = N`
          subst hn_eq
          have hρn : ρVal n = (iSeq n).val := if_pos (le_refl n)
          have hn1_nle : ¬ (n + 1 ≤ n) := by omega
          have hρn1 : ρVal (n + 1) = B_full + ((iSeq (n + 1)).val * P_cnt + p_val) * 2 +
              (if (pSeq n).val = p_val then 1 else 0) := by
            dsimp [ρVal]; rw [if_neg hn1_nle]
          rw [hρn, hρn1, if_pos (iSeq n).isLt]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨(pSeq n).val, (pSeq n).isLt, (iSeq (n + 1)).val, (iSeq (n + 1)).isLt, ?_⟩
          rw [if_pos (hp_ok n)]
          apply List.mem_cons_of_mem
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨p_val, hpo_lt, ?_⟩
          rw [if_pos ⟨hpo_mod, hN n (le_refl n)⟩]
          exact List.mem_singleton.mpr rfl
        · -- Stay in Phase 1 for `n > N`
          have hn_nle : ¬ (n ≤ N) := by omega
          have hn1_nle : ¬ (n + 1 ≤ N) := by omega
          have hρn : ρVal n = B_full + ((iSeq n).val * P_cnt + p_val) * 2 +
              (if (pSeq (n - 1)).val = p_val then 1 else 0) := if_neg hn_nle
          have hρn1 : ρVal (n + 1) = B_full + ((iSeq (n + 1)).val * P_cnt + p_val) * 2 +
              (if (pSeq n).val = p_val then 1 else 0) := by
            dsimp [ρVal]; rw [if_neg hn1_nle]
          have hsub : ρVal n - B_full =
              (if (pSeq (n - 1)).val = p_val then 1 else 0) + 2 * (p_val + P_cnt * (iSeq n).val) := by
            have hmc : (iSeq n).val * P_cnt = P_cnt * (iSeq n).val := Nat.mul_comm _ _
            rw [hρn]; omega
          have hhit_lt : (if (pSeq (n - 1)).val = p_val then 1 else 0) < 2 := by split_ifs <;> decide
          have hd2 : (ρVal n - B_full) / 2 = p_val + P_cnt * (iSeq n).val := by
            rw [hsub, Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt hhit_lt, zero_add]
          have hdiv_i : ((ρVal n - B_full) / 2) / P_cnt = (iSeq n).val := by
            rw [hd2, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hpo_lt, zero_add]
          have hmod_po : ((ρVal n - B_full) / 2) % P_cnt = p_val := by
            rw [hd2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpo_lt]
          have hn_lt_b : ¬ (ρVal n < B_full) := by rw [hρn]; omega
          rw [if_neg hn_lt_b, hdiv_i, hmod_po, if_pos hpo_mod, hρn1]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨(pSeq n).val, (pSeq n).isLt, (iSeq (n + 1)).val, (iSeq (n + 1)).isLt, ?_⟩
          rw [if_pos ⟨hp_ok n, hN n (by omega)⟩]
          exact List.mem_singleton.mpr rfl
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro M
      obtain ⟨m, hm_ge, hm_eq⟩ := hfreq (max M (N + 1))
      refine ⟨m + 1, by omega, ?_⟩
      have hm1_nle : ¬ (m + 1 ≤ N) := by omega
      have hρm1 : (ρ (m + 1)).val = B_full + ((iSeq (m + 1)).val * P_cnt + p_val) * 2 + 1 := by
        change ρVal (m + 1) = _
        dsimp [ρVal, p_val] at hm_eq ⊢
        rw [if_neg hm1_nle]
        simp [hm_eq]
      rw [hρm1]
      simp only [badThreadNBW, List.mem_flatMap, List.mem_range]
      refine ⟨(iSeq (m + 1)).val, (iSeq (m + 1)).isLt, p_val, hpo_lt, ?_⟩
      rw [if_pos hpo_mod]
      exact List.mem_singleton.mpr rfl

lemma primrec_buildTreeSpecAux (E : Thm34Engine) (cOf : ℕ → SymCtx) (hc : Primrec cOf) :
    Primrec fun cn : ℕ => buildTreeSpec E (cOf cn) := by
  have hlbls : Primrec fun cn : ℕ => validSymLabels (cOf cn) := primrec_validSymLabels.comp hc
  have hB : Primrec fun cn : ℕ => ctxBFull (cOf cn) := primrec_ctxBFull.comp hc
  have hL : Primrec fun cn : ℕ => (validSymLabels (cOf cn)).length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hlbls)
  have hroot : Primrec fun cn : ℕ =>
      (List.range ((validSymLabels (cOf cn)).length + 1)).map fun a =>
        if a = 0 then false
        else decide (((validSymLabels (cOf cn)).getD (a - 1) (initSymPos, ([], [], []))).1 = initSymPos) := by
    let R := ℕ × ℕ
    have rcn : Primrec fun r : R => r.1 := Primrec.fst
    have ra : Primrec fun r : R => r.2 := Primrec.snd
    have rpa := (Primrec.list_getD (initSymPos, ([], [], []))).comp (hlbls.comp rcn)
      (Primrec.nat_sub.comp ra (Primrec.const 1))
    exact Primrec.list_map (Primrec.list_range.comp hL)
      (Primrec.ite (Primrec.eq.comp ra (Primrec.const 0)) (Primrec.const false)
        (primrec_decide_eq (Primrec.fst.comp rpa) (Primrec.const initSymPos))).to₂
  have hchild : Primrec fun cn : ℕ =>
      let labels := validSymLabels (cOf cn)
      let B_full := ctxBFull (cOf cn)
      let L_sym := labels.length + 1
      (List.range L_sym).flatMap fun a =>
        (List.range B_full).flatMap fun d =>
          (List.range L_sym).map fun a' =>
            if a = 0 then decide (a' = 0)
            else
              let pa := labels.getD (a - 1) (initSymPos, ([], [], []))
              let comps := symComponents E (cOf cn) pa.1 pa.2
              if d < comps.length then
                if a' = 0 then false
                else
                  let pa' := labels.getD (a' - 1) (initSymPos, ([], [], []))
                  decide (pa'.1 = childSymPos (ctxI (cOf cn)) pa.1 (comps.getD d []))
              else decide (a' = 0) := by
    let R := ((ℕ × ℕ) × ℕ) × ℕ
    have rcn : Primrec fun r : R => r.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have rc : Primrec fun r : R => cOf r.1.1.1 := hc.comp rcn
    have ra : Primrec fun r : R => r.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have rd : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
    have ra' : Primrec fun r : R => r.2 := Primrec.snd
    have rpa := (Primrec.list_getD (initSymPos, ([], [], []))).comp (hlbls.comp rcn)
      (Primrec.nat_sub.comp ra (Primrec.const 1))
    have rpa' := (Primrec.list_getD (initSymPos, ([], [], []))).comp (hlbls.comp rcn)
      (Primrec.nat_sub.comp ra' (Primrec.const 1))
    have rcomps := primrec_symComponentsOf E rc (Primrec.fst.comp rpa) (Primrec.snd.comp rpa)
    have rcomp := (Primrec.list_getD ([] : List SymExtElem)).comp rcomps rd
    have rchildPos := primrec_childSymPosOf (primrec_ctxI.comp rc) (Primrec.fst.comp rpa) rcomp
    have ra'_zero := primrec_decide_eq ra' (Primrec.const 0)
    have rcell := Primrec.ite (Primrec.eq.comp ra (Primrec.const 0))
      ra'_zero
      (Primrec.ite (Primrec.nat_lt.comp rd (Primrec.list_length.comp rcomps))
        (Primrec.ite (Primrec.eq.comp ra' (Primrec.const 0)) (Primrec.const false)
          (primrec_decide_eq (Primrec.fst.comp rpa') rchildPos))
        ra'_zero)
    exact Primrec.list_flatMap (Primrec.list_range.comp hL)
      (Primrec.list_flatMap (Primrec.list_range.comp (hB.comp Primrec.fst))
        (Primrec.list_map (Primrec.list_range.comp (hL.comp (Primrec.fst.comp Primrec.fst)))
          rcell.to₂).to₂).to₂
  have hαMon : Primrec fun cn : ℕ => ((validSymLabels (cOf cn)).length + 1) * ctxBFull (cOf cn) - 1 :=
    Primrec.nat_sub.comp (Primrec.nat_mul.comp hL hB) (Primrec.const 1)
  have hdpa : Primrec fun cn : ℕ =>
      complementGenDPA (E.detListNBW (((validSymLabels (cOf cn)).length + 1) * ctxBFull (cOf cn) - 1)
        (badThreadNBW E (cOf cn) (validSymLabels (cOf cn)))) :=
    primrec_complementGenDPA.comp
      (E.primrec_detListNBW.comp hαMon (primrec_badThreadNBWNat E cOf _ hc hlbls))
  exact ((Primrec.nat_sub.comp hB (Primrec.const 1)).pair
    ((Primrec.list_length.comp hlbls).pair
      (hroot.pair (hchild.pair
        ((Primrec.fst.comp hdpa).pair
          ((Primrec.fst.comp (Primrec.snd.comp hdpa)).pair
            (Primrec.snd.comp (Primrec.snd.comp hdpa)))))))).of_eq fun _ => rfl

lemma primrec_buildTreeSpec (E : Thm34Engine) : Primrec (buildTreeSpec E) :=
  ((primrec_buildTreeSpecAux E unpackCtx primrec_unpackCtx).comp primrec_packCtx).of_eq fun c => by
    simp only [unpackCtx_packCtx]

lemma tsDPA_buildTreeSpec_accepts_iff (E : Thm34Engine) (c : SymCtx)
    (ad : ℕ → Fin ((buildTreeSpec E c).2.1 + 1) × Fin ((buildTreeSpec E c).1 + 1)) :
    (tsDPA (buildTreeSpec E c)).Accepts ad ↔
      ¬ ∃ (iSeq : ℕ → Fin (ctxBFull c)) (pSeq : ℕ → Fin (maxList (ctxBCode c).2.2 + 1)),
        (iSeq 0).val = 0 ∧
        (∀ n, edgeStepOk E c (validSymLabels c) (ad n).1.val (ad n).2.val
          (iSeq n).val (pSeq n).val (iSeq (n + 1)).val = true) ∧
        OddParityCond (fun n => (pSeq n).val) := by
  let labels := validSymLabels c
  let B_full := ctxBFull c
  have hB_succ : (buildTreeSpec E c).1 + 1 = B_full :=
    Nat.sub_add_cancel (ctxBFull_pos c)
  let L_sym := labels.length + 1
  have hα_pos : 0 < L_sym * B_full := Nat.mul_pos (Nat.succ_pos _) (ctxBFull_pos c)
  let αMon := L_sym * B_full - 1
  have hα_succ : αMon + 1 = L_sym * B_full := Nat.sub_add_cancel hα_pos
  let dpaGood := complementGenDPA (E.detListNBW αMon (badThreadNBW E c labels))
  let ad' : ℕ → Fin L_sym × Fin B_full := fun n =>
    (⟨(ad n).1.val, (ad n).1.isLt⟩, ⟨(ad n).2.val, (ad n).2.isLt.trans_eq hB_succ⟩)
  let w : ℕ → Fin (αMon + 1) := fun n =>
    ⟨(ad' n).1.val * B_full + (ad' n).2.val, by
      rw [hα_succ]
      have h1 : (ad' n).1.val + 1 ≤ L_sym := (ad' n).1.isLt
      calc
        (ad' n).1.val * B_full + (ad' n).2.val < (ad' n).1.val * B_full + B_full :=
          Nat.add_lt_add_left (ad' n).2.isLt _
        _ = ((ad' n).1.val + 1) * B_full := by ring
        _ ≤ L_sym * B_full := Nat.mul_le_mul_right B_full h1⟩
  have hrun_eq : ∀ t, ((tsDPA (buildTreeSpec E c)).run ad t).val =
      ((toGenDPA αMon dpaGood).run w t).val := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      have hts_step : ((tsDPA (buildTreeSpec E c)).run ad (t + 1)).val =
          (dpaGood.2.1.getD
            ((((tsDPA (buildTreeSpec E c)).run ad t).val * L_sym + (ad' t).1.val) *
              ((buildTreeSpec E c).1 + 1) + (ad' t).2.val) 0) % (dpaGood.1 + 1) := rfl
      have hgen_step : ((toGenDPA αMon dpaGood).run w (t + 1)).val =
          (dpaGood.2.1.getD
            (((toGenDPA αMon dpaGood).run w t).val * (αMon + 1) +
              ((ad' t).1.val * B_full + (ad' t).2.val)) 0) % (dpaGood.1 + 1) := rfl
      rw [hts_step, hgen_step, ih, hB_succ]
      have hidx : ∀ qv : ℕ,
          (qv * L_sym + (ad' t).1.val) * B_full + (ad' t).2.val =
            qv * (αMon + 1) + ((ad' t).1.val * B_full + (ad' t).2.val) :=
        fun qv => by rw [hα_succ]; ring
      rw [hidx]
  have hacc_eq : (tsDPA (buildTreeSpec E c)).Accepts ad ↔ (toGenDPA αMon dpaGood).Accepts w := by
    unfold DPA.Accepts
    have hfn : (fun t => (tsDPA (buildTreeSpec E c)).prio ((tsDPA (buildTreeSpec E c)).run ad t)) =
        (fun t => (toGenDPA αMon dpaGood).prio ((toGenDPA αMon dpaGood).run w t)) := by
      funext t
      change dpaGood.2.2.getD ((tsDPA (buildTreeSpec E c)).run ad t).val 0 =
        dpaGood.2.2.getD ((toGenDPA αMon dpaGood).run w t).val 0
      rw [hrun_eq t]
    rw [hfn]
  rw [hacc_eq, complementGenDPA_accepts_iff, E.detListNBW_accepts_iff]
  exact not_congr (badThreadNBW_accepts_iff E c labels ad')

lemma tsRootOk_buildTreeSpec (E : Thm34Engine) (c : SymCtx)
    (a : Fin ((buildTreeSpec E c).2.1 + 1)) :
    tsRootOk (buildTreeSpec E c) a =
      if a.val = 0 then false
      else decide (((validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))).1 = initSymPos) := by
  have ha : a.val < (validSymLabels c).length + 1 := a.isLt
  unfold tsRootOk buildTreeSpec
  dsimp only
  rw [getD_eq_getElem _ false a.val (by simp [ha])]
  simp

lemma tsChildOk_buildTreeSpec (E : Thm34Engine) (c : SymCtx)
    (a : Fin ((buildTreeSpec E c).2.1 + 1))
    (d : Fin ((buildTreeSpec E c).1 + 1))
    (a' : Fin ((buildTreeSpec E c).2.1 + 1)) :
    tsChildOk (buildTreeSpec E c) a d a' =
      if a.val = 0 then decide (a'.val = 0)
      else
        let pa := (validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))
        let comps := symComponents E c pa.1 pa.2
        if d.val < comps.length then
          if a'.val = 0 then false
          else
            let pa' := (validSymLabels c).getD (a'.val - 1) (initSymPos, ([], [], []))
            decide (pa'.1 = childSymPos (ctxI c) pa.1 (comps.getD d.val []))
        else decide (a'.val = 0) := by
  have hB_succ : (buildTreeSpec E c).1 + 1 = ctxBFull c := Nat.sub_add_cancel (ctxBFull_pos c)
  let L := (validSymLabels c).length + 1
  let B := ctxBFull c
  have ha_lt : a.val < L := a.isLt
  have hd_lt : d.val < B := d.isLt.trans_eq hB_succ
  have ha'_lt : a'.val < L := a'.isLt
  have hflat3 : ∀ (f : ℕ → ℕ → ℕ → Bool),
      ((List.range L).flatMap fun x => (List.range B).flatMap fun y => (List.range L).map (f x y)).getD
        ((a.val * B + d.val) * L + a'.val) false = f a.val d.val a'.val := by
    intro f
    have hflat2 : ∀ (R C_len : ℕ) (g : ℕ → ℕ → Bool) (r c0 : ℕ) (hr : r < R) (hc0 : c0 < C_len),
        ((List.range R).flatMap fun x => (List.range C_len).map (g x)).getD (r * C_len + c0) false = g r c0 := by
      intro R C_len g r c0 hr hc0
      induction R with
      | zero => cases hr
      | succ R ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        have hlen_p : ((List.range R).flatMap fun x => (List.range C_len).map (g x)).length = R * C_len := by
          simp [List.length_flatMap, List.map_const']
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hr_lt
        · rw [getD_eq_getElem _ false _ (by simp [hlen_p]; omega), List.getElem_append_right (by omega)]
          simp [hlen_p]
        · have hlt_p : r * C_len + c0 < R * C_len := by
            have h1 : r + 1 ≤ R := hr_lt
            calc r * C_len + c0 < r * C_len + C_len := Nat.add_lt_add_left hc0 _
              _ = (r + 1) * C_len := by ring
              _ ≤ R * C_len := Nat.mul_le_mul_right C_len h1
          rw [getD_eq_getElem _ false _ (by simp [hlen_p]; omega),
            List.getElem_append_left (by omega), ← getD_eq_getElem _ false _ (by omega)]
          exact ih hr_lt
    have hrew : ∀ x : ℕ, ((List.range B).flatMap fun y => (List.range L).map (f x y)) =
        (List.range (B * L)).map (fun yz => f x (yz / L) (yz % L)) := by
      intro x
      apply List.ext_getElem
      · simp [List.length_flatMap, List.map_const']
      · intro idx hi1 hi2
        have hi_lt : idx < B * L := by simpa using hi2
        have hL_pos : 0 < L := Nat.succ_pos _
        have hdiv_lt : idx / L < B := (Nat.div_lt_iff_lt_mul hL_pos).mpr hi_lt
        have hmod_lt : idx % L < L := Nat.mod_lt _ hL_pos
        have heq_idx : idx = (idx / L) * L + idx % L := by have := Nat.div_add_mod idx L; linarith
        conv_lhs => rw [← getD_eq_getElem _ false idx hi1, heq_idx]
        rw [hflat2 B L (f x) (idx / L) (idx % L) hdiv_lt hmod_lt]
        simp
    simp only [hrew]
    have hBL_lt : d.val * L + a'.val < B * L := by
      have h1 : d.val + 1 ≤ B := hd_lt
      calc d.val * L + a'.val < d.val * L + L := Nat.add_lt_add_left ha'_lt _
        _ = (d.val + 1) * L := by ring
        _ ≤ B * L := Nat.mul_le_mul_right L h1
    have hidx_eq : (a.val * B + d.val) * L + a'.val = a.val * (B * L) + (d.val * L + a'.val) := by ring
    rw [hidx_eq, hflat2 L (B * L) _ a.val (d.val * L + a'.val) ha_lt hBL_lt]
    have hL_pos : 0 < L := Nat.succ_pos _
    have hsub : d.val * L + a'.val = a'.val + L * d.val := by ring
    rw [hsub, Nat.add_mul_div_left _ _ hL_pos, Nat.div_eq_of_lt ha'_lt, zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha'_lt]
  have hidx : ∀ av dv a'v : ℕ,
      (av * ((buildTreeSpec E c).1 + 1) + dv) * ((buildTreeSpec E c).2.1 + 1) + a'v =
        (av * B + dv) * L + a'v :=
    fun av dv a'v => by rw [hB_succ]; rfl
  unfold tsChildOk
  rw [hidx a.val d.val a'.val]
  exact hflat3 _

lemma length_flatMap_le {α β : Type} (xs : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ xs, (f a).length ≤ M) :
    (xs.flatMap f).length ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hx := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    calc
      (f x).length + (xs.flatMap f).length ≤ M + xs.length * M := Nat.add_le_add hx hxs
      _ = (xs.length + 1) * M := by ring

lemma mem_symLiveExts_iff (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode)
    (e : SymExtElem) :
    e ∈ symLiveExts E ctx pos act ↔
      e.1 ∈ fixedIdxs pos act ∧
      e.2.1 ∈ fullBlocks (ctxI ctx) (ctxD ctx) ∧
      e.2.2 = symNextState E ctx pos act e.1 e.2.1 ∧
      (ctxLive ctx).getD e.2.2 false = true := by
  rcases e with ⟨i, u, q'⟩
  simp only [symLiveExts, List.mem_flatMap]
  constructor
  · rintro ⟨i', hi', u', hu', hmem⟩
    split_ifs at hmem with hlive
    · simp only [List.mem_singleton] at hmem
      rcases Prod.mk.inj hmem with ⟨rfl, hmem2⟩
      rcases Prod.mk.inj hmem2 with ⟨rfl, rfl⟩
      exact ⟨hi', hu', rfl, hlive⟩
    · simp at hmem
  · rintro ⟨hi, hu, rfl, hlive⟩
    exact ⟨i, hi, u, hu, by rw [if_pos hlive]; exact List.mem_singleton.mpr rfl⟩

lemma symLiveExts_nodup_and_length (E : Thm34Engine) (ctx : SymCtx)
    (pos : SymPosCode) (act : SymActCode)
    (hfix_le : (fixedIdxs pos act).length ≤ ctxBRed ctx) :
    (symLiveExts E ctx pos act).Nodup ∧
      (symLiveExts E ctx pos act).length ≤ ctxBFull ctx := by
  let I := ctxI ctx
  let D := ctxD ctx
  have hfix_nd : (fixedIdxs pos act).Nodup := List.Nodup.filter _ List.nodup_range
  have hblk_nd : (fullBlocks I D).Nodup := nodup_fullBlocks I D
  have hblk_len : (fullBlocks I D).length = ctxBlockCard ctx := by
    rw [length_fullBlocks, ctxBlockCard, myPow_eq]
  refine ⟨?_, ?_⟩
  · unfold symLiveExts
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun u _ => by dsimp only; split_ifs <;> simp, ?_⟩
      refine hblk_nd.pairwise_of_forall_ne fun u1 _ u2 _ hne => ?_
      unfold Function.onFun
      rw [List.disjoint_left]
      intro e he1 he2
      dsimp only at he1 he2
      split_ifs at he1 with hl1 <;> [skip; simp at he1]
      split_ifs at he2 with hl2 <;> [skip; simp at he2]
      simp only [List.mem_singleton] at he1 he2
      exact hne (congrArg (fun x : SymExtElem => x.2.1) (he1.symm.trans he2))
    · refine hfix_nd.pairwise_of_forall_ne fun i1 _ i2 _ hne => ?_
      unfold Function.onFun
      rw [List.disjoint_left]
      intro e he1 he2
      simp only [List.mem_flatMap] at he1 he2
      rcases he1 with ⟨u1, _, hm1⟩
      rcases he2 with ⟨u2, _, hm2⟩
      split_ifs at hm1 with hl1 <;> [skip; simp at hm1]
      split_ifs at hm2 with hl2 <;> [skip; simp at hm2]
      simp only [List.mem_singleton] at hm1 hm2
      exact hne (congrArg Prod.fst (hm1.symm.trans hm2))
  · unfold symLiveExts
    have hrow_len : ∀ i ∈ fixedIdxs pos act,
        ((fullBlocks I D).flatMap fun u =>
          let q' := symNextState E ctx pos act i u
          if (ctxLive ctx).getD q' false = true then [(i, u, q')] else []).length ≤ ctxBlockCard ctx := by
      intro i _
      calc
        _ ≤ (fullBlocks I D).length * 1 :=
          length_flatMap_le _ _ 1 (fun u _ => by dsimp only; split_ifs <;> simp)
        _ = ctxBlockCard ctx := by simp [hblk_len]
    calc
      _ ≤ (fixedIdxs pos act).length * ctxBlockCard ctx :=
        length_flatMap_le _ _ (ctxBlockCard ctx) hrow_len
      _ ≤ ctxBRed ctx * ctxBlockCard ctx := Nat.mul_le_mul_right _ hfix_le
      _ = ctxBFull ctx := rfl

lemma symComponents_props (E : Thm34Engine) (ctx : SymCtx)
    (pos : SymPosCode) (act : SymActCode)
    (hfix_le : (fixedIdxs pos act).length ≤ ctxBRed ctx) :
    let S := symLiveExts E ctx pos act
    let comps := symComponents E ctx pos act
    comps.length ≤ ctxBFull ctx ∧
    ∀ (d : ℕ) (hd : d < comps.length),
      let comp := comps[d]'hd
      1 ≤ comp.length ∧ comp.length ≤ ctxBFull ctx ∧ comp.Nodup ∧
      (∀ e ∈ comp, e ∈ S) ∧
      ((∀ a ∈ S, ∀ b ∈ S, symExtAdj (ctxI ctx) pos a b = symExtAdj (ctxI ctx) pos b a) →
        ∀ j1 j2 : Fin comp.length,
          Relation.ReflTransGen
            (fun x y : Fin comp.length => symExtAdj (ctxI ctx) pos comp[x] comp[y] = true) j1 j2) := by
  obtain ⟨hS_nd, hS_len⟩ := symLiveExts_nodup_and_length E ctx pos act hfix_le
  let S := symLiveExts E ctx pos act
  let adj := symExtAdj (ctxI ctx) pos
  let cIdxs := componentsIdx inhSymExt S adj
  have hc_len : (symComponents E ctx pos act).length ≤ ctxBFull ctx := by
    simp only [symComponents, List.length_map]
    exact le_trans (componentsIdx_length_le inhSymExt S adj) hS_len
  refine ⟨hc_len, fun d hd => ?_⟩
  have hd_ci : d < cIdxs.length := by simpa [symComponents, cIdxs] using hd
  let idxs := cIdxs[d]'hd_ci
  have hidxs_mem : idxs ∈ cIdxs := List.getElem_mem hd_ci
  dsimp only [cIdxs] at hidxs_mem
  unfold componentsIdx at hidxs_mem
  rw [mem_dedupList, List.mem_map] at hidxs_mem
  rcases hidxs_mem with ⟨i0, hi0_r, hidxs_eq⟩
  have hi0_lt : i0 < S.length := List.mem_range.mp hi0_r
  obtain ⟨hnd_i, hi0_in, hlen_i, hall_lt⟩ := compIdxOf_nodup_and_lt inhSymExt S adj hi0_lt
  rw [hidxs_eq] at hnd_i hi0_in hlen_i hall_lt
  let comp := (symComponents E ctx pos act)[d]'hd
  have hcomp_eq : comp = idxs.map (fun idx => S.getD idx inhSymExt) := by
    simp only [comp, idxs, cIdxs, S, adj, symComponents, List.getElem_map]
  have hcomp_len : comp.length = idxs.length := by simp [hcomp_eq]
  have hk1 : 1 ≤ comp.length := by
    rw [hcomp_len]
    exact List.length_pos_of_mem hi0_in
  have hkB : comp.length ≤ ctxBFull ctx := by
    rw [hcomp_len]; exact le_trans hlen_i hS_len
  have hcomp_nd : comp.Nodup := by
    rw [hcomp_eq, List.nodup_map_iff_inj_on hnd_i]
    intro a ha b hb heq
    have ha_lt := hall_lt a ha
    have hb_lt := hall_lt b hb
    rw [getD_eq_getElem S inhSymExt a ha_lt, getD_eq_getElem S inhSymExt b hb_lt] at heq
    exact (List.Nodup.getElem_inj_iff hS_nd).mp heq
  have hcomp_in_S : ∀ e ∈ comp, e ∈ S := by
    intro e he
    rw [hcomp_eq, List.mem_map] at he
    rcases he with ⟨idx, hidx, rfl⟩
    rw [getD_eq_getElem S inhSymExt idx (hall_lt idx hidx)]
    exact List.getElem_mem (hall_lt idx hidx)
  refine ⟨hk1, hkB, hcomp_nd, hcomp_in_S, fun hsym j1 j2 => ?_⟩
  let R_S := fun a b : ℕ => a < S.length ∧ b < S.length ∧ adj (S.getD a inhSymExt) (S.getD b inhSymExt) = true
  let R_c := fun x y : Fin comp.length => adj comp[x] comp[y] = true
  have hcomp_at : ∀ j : Fin comp.length,
      comp[j] = S.getD (idxs[j.val]'(hcomp_len ▸ j.isLt)) inhSymExt := by
    intro j; simp [hcomp_eq]
  obtain ⟨hj0_lt_i, hj0_get⟩ := cIdxOf_lt_and_getElem hi0_in
  let j0 : Fin comp.length := ⟨cIdxOf idxs i0, hcomp_len.symm ▸ hj0_lt_i⟩
  have hj0_idx : idxs[j0.val]'(hcomp_len ▸ j0.isLt) = i0 := hj0_get
  have hlift : ∀ {y : ℕ}, Relation.ReflTransGen R_S i0 y →
      ∀ (jy : Fin comp.length), idxs[jy.val]'(hcomp_len ▸ jy.isLt) = y →
        Relation.ReflTransGen R_c j0 jy := by
    intro y hr
    induction hr with
    | refl =>
      intro jy hjy
      have heq_j : jy = j0 := Fin.ext ((List.Nodup.getElem_inj_iff hnd_i).mp (hjy.trans hj0_idx.symm))
      subst heq_j; exact .refl
    | @tail a b h_i0_a h_ab ih =>
      intro jb hjb
      have ha_in : a ∈ idxs := by
        rw [← hidxs_eq, mem_compIdxOf_iff inhSymExt S adj hi0_lt a]
        exact ⟨h_ab.1, h_i0_a⟩
      obtain ⟨hja_lt_i, hja_get⟩ := cIdxOf_lt_and_getElem ha_in
      let ja : Fin comp.length := ⟨cIdxOf idxs a, hcomp_len.symm ▸ hja_lt_i⟩
      have hja_idx : idxs[ja.val]'(hcomp_len ▸ ja.isLt) = a := hja_get
      have hr_ja := ih ja hja_idx
      have hstep_c : R_c ja jb := by
        dsimp only [R_c]
        rw [hcomp_at ja, hcomp_at jb, hja_idx, hjb]
        exact h_ab.2.2
      exact hr_ja.tail hstep_c
  have hr_from_j0 : ∀ j : Fin comp.length, Relation.ReflTransGen R_c j0 j := by
    intro j
    have hj_in : idxs[j.val]'(hcomp_len ▸ j.isLt) ∈ compIdxOf inhSymExt S adj i0 := by
      rw [hidxs_eq]; exact List.getElem_mem _
    obtain ⟨_, hr_j⟩ := (mem_compIdxOf_iff inhSymExt S adj hi0_lt _).mp hj_in
    exact hlift hr_j j rfl
  have hrev_c : ∀ {x y : Fin comp.length}, Relation.ReflTransGen R_c x y → Relation.ReflTransGen R_c y x := by
    intro x y hr
    induction hr with
    | refl => exact .refl
    | @tail u v _ huv ih =>
      have hu_S : comp[u] ∈ S := hcomp_in_S comp[u] (List.getElem_mem u.isLt)
      have hv_S : comp[v] ∈ S := hcomp_in_S comp[v] (List.getElem_mem v.isLt)
      have hvu : R_c v u := by
        dsimp only [R_c, adj] at huv ⊢
        rwa [hsym comp[v] hv_S comp[u] hu_S]
      exact (Relation.ReflTransGen.single hvu).trans ih
  exact (hrev_c (hr_from_j0 j1)).trans (hr_from_j0 j2)

lemma childSymPos_access (I : Instance) (pos : SymPosCode) (comp : List SymExtElem) :
    let pos' := childSymPos I pos comp
    pos'.1 = comp.length ∧
    (∀ a (ha : a < comp.length) b (hb : b < comp.length),
      eq1At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).1) ∧
    (∀ a (ha : a < comp.length) b (hb : b < comp.length),
      eq2At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).2) ∧
    (∀ a (ha : a < comp.length), stateAt pos' a = (comp[a]'ha).2.2) := by
  let k' := comp.length
  have hflat : ∀ (f : ℕ → ℕ → Bool) (a b : ℕ), a < k' → b < k' →
      ((List.range k').flatMap fun x => (List.range k').map (f x)).getD (a * k' + b) false = f a b := by
    intro f a b ha hb
    have hrec : ∀ (R r : ℕ), r < R →
        ((List.range R).flatMap fun x => (List.range k').map (f x)).getD (r * k' + b) false = f r b := by
      intro R r hr
      induction R with
      | zero => cases hr
      | succ R ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        have hlp : ((List.range R).flatMap fun x => (List.range k').map (f x)).length = R * k' := by
          simp [List.length_flatMap, List.map_const']
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hr_lt
        · rw [getD_eq_getElem _ false _ (by simp [hlp, hb]), List.getElem_append_right (by omega)]
          simp [hlp]
        · have hlt_p : r * k' + b < R * k' := by
            have h1 : r + 1 ≤ R := hr_lt
            calc r * k' + b < r * k' + k' := Nat.add_lt_add_left hb _
              _ = (r + 1) * k' := by ring
              _ ≤ R * k' := Nat.mul_le_mul_right k' h1
          rw [getD_eq_getElem _ false _ (by simp [hlp]; omega),
            List.getElem_append_left (by omega), ← getD_eq_getElem _ false _ (by omega)]
          exact ih hr_lt
    exact hrec k' a ha
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro a ha b hb
    unfold eq1At childSymPos
    dsimp only
    rw [hflat _ a b ha hb, getD_eq_getElem comp inhSymExt a ha, getD_eq_getElem comp inhSymExt b hb]
  · intro a ha b hb
    unfold eq2At childSymPos
    dsimp only
    rw [hflat _ a b ha hb, getD_eq_getElem comp inhSymExt a ha, getD_eq_getElem comp inhSymExt b hb]
  · intro a ha
    unfold stateAt childSymPos
    dsimp only
    rw [getD_eq_getElem _ 0 a (by simp [ha])]
    simp

end DistLTLSynth.Char.Lemma313Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma313Aux in
theorem solution :
    (Primrec parseOk) ∧
    (∀ ts : List Token, parseOk ts = true ↔ ∃ φ, parse ts = some φ) ∧
    (∀ (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ) (A : Set (ℕ → CommGraph)) (f : Algorithm I.X1 I.X2 I.Y1 I.Y2),
      FRealizes f A (instFormulaOf I φ) ↔ RealizesLang f A (I.Lang φ)) ∧
    (Primrec validSymLabels) ∧
    (∀ c : SymCtx, (validSymLabels c).Nodup) ∧
    (∀ (c : SymCtx) (pa : SymPosCode × SymActCode),
      pa ∈ validSymLabels c ↔
        pa.1 ∈ allSymPos c ∧ pa.2 ∈ allSymActsFor c pa.1 ∧ actValid c pa.1 pa.2 = true) ∧
    (∀ E : Thm34Engine, Primrec (symNextStatePacked E)) ∧
    (∀ E : Thm34Engine, Primrec (symComponentsPacked E)) ∧
    (∀ E : Thm34Engine, Primrec (buildTreeSpec E)) ∧
    (∀ (E : Thm34Engine) (c : SymCtx) (a : Fin ((buildTreeSpec E c).2.1 + 1)),
      tsRootOk (buildTreeSpec E c) a =
        if a.val = 0 then false
        else decide (((validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))).1 = initSymPos)) ∧
    (∀ (E : Thm34Engine) (c : SymCtx) (a : Fin ((buildTreeSpec E c).2.1 + 1))
      (d : Fin ((buildTreeSpec E c).1 + 1)) (a' : Fin ((buildTreeSpec E c).2.1 + 1)),
      tsChildOk (buildTreeSpec E c) a d a' =
        if a.val = 0 then decide (a'.val = 0)
        else
          let pa := (validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))
          let comps := symComponents E c pa.1 pa.2
          if d.val < comps.length then
            if a'.val = 0 then false
            else
              let pa' := (validSymLabels c).getD (a'.val - 1) (initSymPos, ([], [], []))
              decide (pa'.1 = childSymPos (ctxI c) pa.1 (comps.getD d.val []))
          else decide (a'.val = 0)) ∧
    (∀ (E : Thm34Engine) (c : SymCtx)
      (ad : ℕ → Fin ((buildTreeSpec E c).2.1 + 1) × Fin ((buildTreeSpec E c).1 + 1)),
      (tsDPA (buildTreeSpec E c)).Accepts ad ↔
        ¬ ∃ (iSeq : ℕ → Fin (ctxBFull c)) (pSeq : ℕ → Fin (maxList (ctxBCode c).2.2 + 1)),
          (iSeq 0).val = 0 ∧
          (∀ n, edgeStepOk E c (validSymLabels c) (ad n).1.val (ad n).2.val
            (iSeq n).val (pSeq n).val (iSeq (n + 1)).val = true) ∧
          OddParityCond (fun n => (pSeq n).val)) ∧
    (∀ (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode) (e : SymExtElem),
      e ∈ symLiveExts E ctx pos act ↔
        e.1 ∈ fixedIdxs pos act ∧
        e.2.1 ∈ fullBlocks (ctxI ctx) (ctxD ctx) ∧
        e.2.2 = symNextState E ctx pos act e.1 e.2.1 ∧
        (ctxLive ctx).getD e.2.2 false = true) ∧
    (∀ (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode),
      (fixedIdxs pos act).length ≤ ctxBRed ctx →
      (symLiveExts E ctx pos act).Nodup ∧ (symLiveExts E ctx pos act).length ≤ ctxBFull ctx) ∧
    (∀ (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode),
      (fixedIdxs pos act).length ≤ ctxBRed ctx →
      let S := symLiveExts E ctx pos act
      let comps := symComponents E ctx pos act
      comps.length ≤ ctxBFull ctx ∧
      ∀ (d : ℕ) (hd : d < comps.length),
        let comp := comps[d]'hd
        1 ≤ comp.length ∧ comp.length ≤ ctxBFull ctx ∧ comp.Nodup ∧
        (∀ e ∈ comp, e ∈ S) ∧
        ((∀ a ∈ S, ∀ b ∈ S, symExtAdj (ctxI ctx) pos a b = symExtAdj (ctxI ctx) pos b a) →
          ∀ j1 j2 : Fin comp.length,
            Relation.ReflTransGen
              (fun x y : Fin comp.length => symExtAdj (ctxI ctx) pos comp[x] comp[y] = true) j1 j2)) ∧
    (∀ (I : Instance) (pos : SymPosCode) (comp : List SymExtElem),
      let pos' := childSymPos I pos comp
      pos'.1 = comp.length ∧
      (∀ a (ha : a < comp.length) b (hb : b < comp.length),
        eq1At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).1) ∧
      (∀ a (ha : a < comp.length) b (hb : b < comp.length),
        eq2At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).2) ∧
      (∀ a (ha : a < comp.length), stateAt pos' a = (comp[a]'ha).2.2)) ∧
    (∀ (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)}, h1.length = h2.length →
      ∀ (w1 w2 : List ℕ),
        extEqFrom I (decide (view1 h1 = view1 h2)) (decide (view2 h1 = view2 h2)) w1 w2 =
          (decide (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2)),
           decide (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2)))) ∧
    (∀ (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)}, h1.length = h2.length →
      ∀ {b1 b2 : Bool}, (view1 h1 = view1 h2 → b1 = true) → (view2 h1 = view2 h2 → b2 = true) →
      ∀ (w1 w2 : List ℕ),
        (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).1 = true) ∧
          (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).2 = true)) ∧
    (∀ {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) {i : ℕ}, i < S.length →
      ∀ y : ℕ,
        y ∈ compIdxOf inh S adj i ↔
          y < S.length ∧
            Relation.ReflTransGen
              (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i y) ∧
    (∀ {α : Type} (inh : α) (S : List α) (adj : α → α → Bool) {i : ℕ}, i < S.length →
      (compIdxOf inh S adj i).Nodup ∧ i ∈ compIdxOf inh S adj i ∧
        (compIdxOf inh S adj i).length ≤ S.length ∧
        ∀ y ∈ compIdxOf inh S adj i, y < S.length) ∧
    (∀ {α : Type} (inh : α) (S : List α) (adj : α → α → Bool),
      (∀ a < S.length, ∀ b < S.length,
        adj (S.getD a inh) (S.getD b inh) = adj (S.getD b inh) (S.getD a inh)) →
      ∀ {i j : ℕ}, i < S.length → j < S.length →
      Relation.ReflTransGen
        (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i j →
      compIdxOf inh S adj i = compIdxOf inh S adj j) :=
  ⟨primrec_parseOk,
   parseOk_iff_exists_parse,
   fRealizes_instFormulaOf_iff,
   primrec_validSymLabels,
   nodup_validSymLabels,
   mem_validSymLabels_iff,
   primrec_symNextStatePacked,
   primrec_symComponentsPacked,
   primrec_buildTreeSpec,
   tsRootOk_buildTreeSpec,
   tsChildOk_buildTreeSpec,
   tsDPA_buildTreeSpec_accepts_iff,
   mem_symLiveExts_iff,
   symLiveExts_nodup_and_length,
   symComponents_props,
   childSymPos_access,
   extEqFrom_exact,
   extEqFrom_of_hom,
   mem_compIdxOf_iff,
   compIdxOf_nodup_and_lt,
   compIdxOf_eq_of_reach⟩
