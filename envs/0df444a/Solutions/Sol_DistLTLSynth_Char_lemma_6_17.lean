-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_6_17
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:46:04.275973+00:00
-- url     : https://prove2.me/submissions/1c49a4fb-2d13-45aa-8210-19442d02b185

import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Theorems.Thm_DistLTLSynth_Char_lemma_6_13

namespace DistLTLSynth.Char.Lemma617Aux
open DistLTLSynth.Char

lemma sat_tt {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.tt : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.tt, Formula.Sat]
  exact em _

lemma sat_bigAnd {X1 X2 Y1 Y2 : Type} (l : List (Formula X1 X2 Y1 Y2))
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.bigAnd l).Sat e ↔ ∀ ψ ∈ l, ψ.Sat e := by
  induction l with
  | nil =>
    simp only [Formula.bigAnd, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    exact sat_tt e
  | cons a tl ih =>
    simp only [Formula.bigAnd, Formula.Sat, ih, List.mem_cons, forall_eq_or_imp]

lemma shift_add {α : Type} (e : ℕ → α) (a b : ℕ) :
    shift (shift e a) b = shift e (a + b) := by
  funext n
  simp only [shift]
  congr 1
  omega

lemma sat_nextIter {X1 X2 Y1 Y2 : Type} (k : ℕ) (ψ : Formula X1 X2 Y1 Y2)
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.nextIter k ψ).Sat e ↔ ψ.Sat (shift e k) := by
  induction k generalizing e with
  | zero =>
    have h0 : shift e 0 = e := by funext n; simp [shift]
    simp [Formula.nextIter, h0]
  | succ k ih =>
    simp only [Formula.nextIter, Formula.Sat, ih, shift_add, Nat.add_comm 1 k]

lemma pre_get {α : Type} (f : ℕ → α) (m k : ℕ) (hk : k < (pre f m).length) :
    (pre f m)[k] = f k := by
  simp only [pre, List.getElem_ofFn]

lemma append_pre_lt {α : Type} (x u : ℕ → α) (m k : ℕ) (hk : k < m) :
    append (pre x m) u k = x k := by
  unfold append
  have hlt : k < (pre x m).length := by simp [pre, hk]
  rw [dif_pos hlt, pre_get]

lemma sat_prefixFormula {X1 X2 Y1 Y2 : Type} (h : List CommGraph)
    (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (prefixFormula h : Formula X1 X2 Y1 Y2).Sat e ↔ pre (graphOfExec e) h.length = h := by
  unfold prefixFormula
  rw [sat_bigAnd]
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro hh
    apply List.ext_getElem
    · simp [pre]
    · intro i h1 h2
      have hi := hh ⟨i, h2⟩
      rw [sat_nextIter] at hi
      simp only [Formula.Sat, shift, zero_add, Fin.getElem_fin] at hi
      rw [pre_get]
      exact hi
  · intro hh i
    rw [sat_nextIter]
    simp only [Formula.Sat, shift, zero_add]
    have hget := congrArg (fun l => l[i.val]?) hh
    simpa [pre, graphOfExec, i.isLt] using hget

lemma sat_hatFormula {X1 X2 Y1 Y2 : Type} (h : List CommGraph)
    (φ : Formula X1 X2 Y1 Y2) (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (hatFormula h φ).Sat e ↔ (pre (graphOfExec e) h.length = h → φ.Sat (shift e h.length)) := by
  unfold hatFormula
  simp only [Formula.Sat, sat_prefixFormula, sat_nextIter]

lemma hatFormula_isSafety {X1 X2 Y1 Y2 : Type} (h : List CommGraph)
    (φ : Formula X1 X2 Y1 Y2) (hφ : φ.IsSafety) :
    (hatFormula h φ).IsSafety := by
  intro t ht
  have ht' : ¬ (pre (graphOfExec t) h.length = h → φ.Sat (shift t h.length)) := by
    intro himp
    exact ht ((sat_hatFormula h φ t).mpr himp)
  rw [Classical.not_imp] at ht'
  obtain ⟨hpre, hnot⟩ := ht'
  obtain ⟨i, hi⟩ := hφ (shift t h.length) hnot
  refine ⟨h.length + i, ?_⟩
  intro u hu
  have hu' := (sat_hatFormula h φ _).mp hu
  have hpre_u : pre (graphOfExec (append (pre t (h.length + i)) u)) h.length = h := by
    refine Eq.trans ?_ hpre
    apply List.ext_getElem
    · simp [pre]
    · intro k hk1 hk2
      rw [pre_get, pre_get]
      have hk : k < h.length + i := by simp [pre] at hk2; omega
      simp only [graphOfExec, append_pre_lt t u (h.length + i) k hk]
  have hshift : shift (append (pre t (h.length + i)) u) h.length =
      append (pre (shift t h.length) i) u := by
    funext m
    simp only [shift, append]
    have hl1 : (pre t (h.length + i)).length = h.length + i := by simp [pre]
    have hl2 : (pre (shift t h.length) i).length = i := by simp [pre]
    by_cases hm : m < i
    · have hm1 : m + h.length < (pre t (h.length + i)).length := by omega
      have hm2 : m < (pre (shift t h.length) i).length := by omega
      rw [dif_pos hm1, dif_pos hm2]
      simp only [pre, List.getElem_ofFn, shift]
    · have hm1 : ¬ (m + h.length < (pre t (h.length + i)).length) := by omega
      have hm2 : ¬ (m < (pre (shift t h.length) i).length) := by omega
      rw [dif_neg hm1, dif_neg hm2]
      congr 1
      omega
  have hsat_shift := hu' hpre_u
  rw [hshift] at hsat_shift
  exact hi u hsat_shift

def toSig (l : List CommGraph) : List (Signal Unit Unit) :=
  l.map (fun g => ((), (), g))

@[simp] lemma toSig_length (l : List CommGraph) : (toSig l).length = l.length := by
  simp [toSig]

@[simp] lemma toSig_append (a b : List CommGraph) : toSig (a ++ b) = toSig a ++ toSig b := by
  simp [toSig]

def seedView (h : List CommGraph) : View Unit Unit → View Unit Unit
  | .I1 => view1 (toSig h)
  | .I2 => view2 (toSig h)
  | .N1 x1 u => .N1 x1 (seedView h u)
  | .N2 x2 v => .N2 x2 (seedView h v)
  | .C1 x1 u x2 v => .C1 x1 (seedView h u) x2 (seedView h v)
  | .C2 x2 v x1 u => .C2 x2 (seedView h v) x1 (seedView h u)

lemma views_append_singleton {X1 X2 : Type} (u : List (Signal X1 X2)) (a : Signal X1 X2) :
    views (u ++ [a]) = viewStep (views u) a := by
  simp [views]

lemma seedView_views (h : List CommGraph) (u : List (Signal Unit Unit)) :
    seedView h (view1 u) = view1 (toSig h ++ u) ∧
      seedView h (view2 u) = view2 (toSig h ++ u) := by
  induction u using List.reverseRecOn with
  | nil => simp [view1, view2, views, seedView]
  | append_singleton u a ih =>
    rcases a with ⟨⟨⟩, ⟨⟩, g⟩
    rw [← List.append_assoc]
    unfold view1 view2 at ih ⊢
    rw [views_append_singleton, views_append_singleton]
    cases g <;> simp [viewStep, seedView, ih.1, ih.2]

def isP1 : View Unit Unit → Bool
  | .I1 | .N1 _ _ | .C1 _ _ _ _ => true
  | .I2 | .N2 _ _ | .C2 _ _ _ _ => false

def vdepth : View Unit Unit → ℕ
  | .I1 | .I2 => 0
  | .N1 _ u | .C1 _ u _ _ => vdepth u + 1
  | .N2 _ v | .C2 _ v _ _ => vdepth v + 1

lemma views_meta (u : List (Signal Unit Unit)) :
    isP1 (view1 u) = true ∧ isP1 (view2 u) = false ∧
      vdepth (view1 u) = u.length ∧ vdepth (view2 u) = u.length := by
  induction u using List.reverseRecOn with
  | nil => simp [view1, view2, views, isP1, vdepth]
  | append_singleton u a ih =>
    rcases a with ⟨⟨⟩, ⟨⟩, g⟩
    unfold view1 view2 at ih ⊢
    rw [views_append_singleton]
    cases g <;> simp [viewStep, isP1, vdepth, ih.2.2.1, ih.2.2.2]

def suffixView : ℕ → View Unit Unit → View Unit Unit
  | 0, w => if isP1 w then .I1 else .I2
  | _ + 1, .I1 => .I1
  | _ + 1, .I2 => .I2
  | n + 1, .N1 x1 u => .N1 x1 (suffixView n u)
  | n + 1, .N2 x2 v => .N2 x2 (suffixView n v)
  | n + 1, .C1 x1 u x2 v => .C1 x1 (suffixView n u) x2 (suffixView n v)
  | n + 1, .C2 x2 v x1 u => .C2 x2 (suffixView n v) x1 (suffixView n u)

lemma suffixView_views (w u : List (Signal Unit Unit)) :
    suffixView u.length (view1 (w ++ u)) = view1 u ∧
      suffixView u.length (view2 (w ++ u)) = view2 u := by
  induction u using List.reverseRecOn with
  | nil =>
    have hm := views_meta w
    simp only [List.append_nil, List.length_nil, suffixView, hm.1, hm.2.1]
    exact ⟨rfl, rfl⟩
  | append_singleton u a ih =>
    rcases a with ⟨⟨⟩, ⟨⟩, g⟩
    rw [← List.append_assoc]
    simp only [List.length_append, List.length_singleton]
    unfold view1 view2 at ih ⊢
    rw [views_append_singleton, views_append_singleton]
    cases g <;> simp [viewStep, suffixView, ih.1, ih.2]

lemma pre_add_split {α : Type} (s : ℕ → α) (a b : ℕ) :
    pre s (a + b) = pre s a ++ pre (shift s a) b := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2
    simp only [pre, List.length_ofFn] at h1
    by_cases hi : i < a
    · rw [List.getElem_append_left (by simp [pre, hi])]
      simp only [pre, List.getElem_ofFn]
    · rw [List.getElem_append_right (by simp [pre]; omega)]
      simp only [pre, List.length_ofFn, List.getElem_ofFn, shift]
      congr 1
      omega

lemma continuous_append_graphs (h : List CommGraph) :
    Continuous (append h : (ℕ → CommGraph) → (ℕ → CommGraph)) := by
  apply continuous_pi
  intro n
  unfold append
  by_cases hn : n < h.length
  · simpa [hn] using (continuous_const : Continuous (fun _ : ℕ → CommGraph => h[n]))
  · simpa [hn] using continuous_apply (n - h.length)

lemma append_mem_closure_of_dense (A : Set (ℕ → CommGraph)) (h : List CommGraph)
    (hdense : Dense (leftQuot h A)) (x : ℕ → CommGraph) :
    append h x ∈ closure A :=
  map_mem_closure (continuous_append_graphs h) (hdense x) (fun _ hk => hk)

end DistLTLSynth.Char.Lemma617Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma617Aux in
theorem solution {Y1 Y2 : Type} [Fintype Y1] [Nonempty Y1] [Fintype Y2] [Nonempty Y2]
    (A : Set (ℕ → CommGraph)) (h : List CommGraph) (hdense : Dense (leftQuot h A))
    (φ : Formula Unit Unit Y1 Y2) (hφ : φ.IsSafety) :
    Realizable Set.univ φ ↔ Realizable A (hatFormula h φ) := by
  constructor
  · rintro ⟨f, hf⟩
    let resetAlg : Algorithm Unit Unit Y1 Y2 :=
      ⟨fun v => f.f1 (suffixView (vdepth v - h.length) v),
       fun v => f.f2 (suffixView (vdepth v - h.length) v)⟩
    refine ⟨resetAlg, fun s _ => ?_⟩
    change (hatFormula h φ).Sat (exec resetAlg s)
    rw [sat_hatFormula]
    intro _
    have hshift : shift (exec resetAlg s) h.length = exec f (shift s h.length) := by
      funext n
      have hlen : n + h.length + 1 = h.length + (n + 1) := by omega
      have hsp := pre_add_split s h.length (n + 1)
      have hm := views_meta (pre s h.length ++ pre (shift s h.length) (n + 1))
      have hlen_u : (pre (shift s h.length) (n + 1)).length = n + 1 := by simp [pre]
      have hlen_w : (pre s h.length).length = h.length := by simp [pre]
      have hd1 : vdepth (view1 (pre s (n + h.length + 1))) - h.length = n + 1 := by
        rw [hlen, hsp, hm.2.2.1, List.length_append, hlen_w, hlen_u]; omega
      have hd2 : vdepth (view2 (pre s (n + h.length + 1))) - h.length = n + 1 := by
        rw [hlen, hsp, hm.2.2.2, List.length_append, hlen_w, hlen_u]; omega
      have hsuf := suffixView_views (pre s h.length) (pre (shift s h.length) (n + 1))
      rw [hlen_u] at hsuf
      simp only [shift, exec, resetAlg, hd1, hd2]
      rw [hlen, hsp, hsuf.1, hsuf.2]
    rw [hshift]
    exact hf (shift s h.length) (Set.mem_univ _)
  · rintro ⟨τ, hτ⟩
    have hclos : FRealizes τ (closure A) (hatFormula h φ) :=
      (lemma_6_13 A (hatFormula h φ) (hatFormula_isSafety h φ hφ) τ).mp hτ
    let seedAlg : Algorithm Unit Unit Y1 Y2 :=
      ⟨fun v => τ.f1 (seedView h v), fun v => τ.f2 (seedView h v)⟩
    refine ⟨seedAlg, fun s _ => ?_⟩
    let x : ℕ → CommGraph := graphOf s
    let sFull : ℕ → Signal Unit Unit := fun n => ((), (), append h x n)
    have hmem : graphOf sFull ∈ closure A := by
      change append h x ∈ closure A
      exact append_mem_closure_of_dense A h hdense x
    have hsatFull : (hatFormula h φ).Sat (exec τ sFull) := hclos sFull hmem
    rw [sat_hatFormula] at hsatFull
    have hpreEq : pre (graphOfExec (exec τ sFull)) h.length = h := by
      apply List.ext_getElem
      · simp [pre]
      · intro i hi1 hi2
        simp only [pre, List.getElem_ofFn, graphOfExec, exec, sFull, append, dif_pos hi2]
    have hsatShift : φ.Sat (shift (exec τ sFull) h.length) := hsatFull hpreEq
    have hexecEq : exec seedAlg s = shift (exec τ sFull) h.length := by
      funext n
      have hs_eq : s n = ((), (), x n) := by
        rcases hs : s n with ⟨⟨⟩, ⟨⟩, g⟩
        simp [x, graphOf, hs]
      have hsFull_n : sFull (n + h.length) = s n := by
        rw [hs_eq]
        simp only [sFull, append]
        have hn : ¬ (n + h.length < h.length) := by omega
        rw [dif_neg hn, Nat.add_sub_cancel]
      have hpreFull : pre sFull (n + h.length + 1) = toSig h ++ pre s (n + 1) := by
        apply List.ext_getElem
        · simp only [pre, List.length_ofFn, List.length_append, toSig_length]; omega
        · intro k hk1 hk2
          rw [pre_get]
          by_cases hk : k < h.length
          · rw [List.getElem_append_left (by simp [toSig, hk])]
            simp only [sFull, append, dif_pos hk, toSig, List.getElem_map]
          · rw [List.getElem_append_right (by simp [toSig]; omega)]
            simp only [toSig_length]
            rw [pre_get]
            have hs_sub : s (k - h.length) = ((), (), x (k - h.length)) := by
              rcases hsk : s (k - h.length) with ⟨⟨⟩, ⟨⟩, g⟩
              simp [x, graphOf, hsk]
            simp only [sFull, append, dif_neg hk, hs_sub]
      have hseed := seedView_views h (pre s (n + 1))
      simp only [exec, shift, seedAlg, hsFull_n, hpreFull, hseed.1, hseed.2]
    change φ.Sat (exec seedAlg s)
    rwa [hexecEq]
