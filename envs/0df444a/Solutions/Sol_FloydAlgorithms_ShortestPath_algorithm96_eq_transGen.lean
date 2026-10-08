-- Prove2me | solution 1 for FloydAlgorithms.ShortestPath.algorithm96_eq_transGen
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T14:57:56.723451+00:00
-- url     : https://prove2.me/submissions/d0d6e1ad-e54f-4cf2-8a43-034fa641ba75

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96



namespace FloydAlgorithms.ShortestPath

namespace A96

variable {n : ℕ}

abbrev BM (n : ℕ) := Fin n → Fin n → Bool

def kstep (i j : Fin n) (m : BM n) (k : Fin n) : BM n :=
  if m i k then Function.update m j (Function.update (m j) k true) else m

def G (m0 : BM n) (i j : Fin n) (S : List (Fin n)) : BM n :=
  Function.update m0 j (fun k => if k ∈ S then (m0 j k || (m0 j i && m0 i k)) else m0 j k)

lemma G_jk (m0 : BM n) (i j k : Fin n) (S : List (Fin n)) (hk : k ∉ S) :
    G m0 i j S j k = m0 j k := by
  simp [G, hk]

lemma G_ik (m0 : BM n) (i j k : Fin n) (S : List (Fin n)) (hk : k ∉ S) :
    G m0 i j S i k = m0 i k := by
  by_cases h : i = j
  · subst h; simp [G, hk]
  · simp [G, Function.update_apply, h]

lemma G_ji (m0 : BM n) (i j : Fin n) (S : List (Fin n)) :
    G m0 i j S j i = m0 j i := by
  simp only [G, Function.update_self]
  split_ifs <;> cases m0 j i <;> simp

lemma kloop (m0 : BM n) (i j : Fin n) (hji : m0 j i = true) :
    ∀ (l S : List (Fin n)), l.Nodup → (∀ x ∈ l, x ∉ S) →
      l.foldl (kstep i j) (G m0 i j S) = G m0 i j (l ++ S) := by
  intro l
  induction l with
  | nil => intro S _ _; simp
  | cons k l ih =>
    intro S hnd hdis
    rw [List.foldl_cons]
    have hk : k ∉ S := hdis k (by simp)
    have hstep : kstep i j (G m0 i j S) k = G m0 i j (k :: S) := by
      have e1 := G_ik m0 i j k S hk
      have e2 := G_jk m0 i j k S hk
      have e3 := G_ji m0 i j S
      funext a c
      unfold kstep
      rw [e1]
      by_cases ha : a = j
      · subst ha
        by_cases hc : c = k
        · subst hc
          cases h1 : m0 i c <;> simp [G, h1, hk, hji]
        · cases h1 : m0 i k <;> simp [G, h1, hc, Function.update_apply]
      · cases h1 : m0 i k <;> simp [G, h1, ha, Function.update_apply]
    rw [hstep, ih (k :: S) (List.nodup_cons.mp hnd).2 ?_]
    · have hm : ∀ x, x ∈ l ++ k :: S ↔ x ∈ k :: l ++ S := by
        intro x; simp only [List.mem_append, List.mem_cons]; tauto
      unfold G; simp only [hm]
    · intro x hx hxS
      rcases List.mem_cons.mp hxS with h | h
      · subst h; exact (List.nodup_cons.mp hnd).1 hx
      · exact hdis x (by simp [hx]) h

def rowS (i j : Fin n) (m : BM n) : BM n :=
  if m j i then (List.finRange n).foldl (kstep i j) m else m

lemma rowS_eq (i j : Fin n) (m : BM n) :
    rowS i j m = Function.update m j (fun k => m j k || (m j i && m i k)) := by
  unfold rowS
  have hG : G m i j [] = m := by
    funext a c; by_cases ha : a = j
    · subst ha; simp [G]
    · simp [G, ha]
  split_ifs with h
  · conv_lhs => rw [← hG]
    rw [kloop m i j h _ [] (List.nodup_finRange n) (by simp)]
    simp [G]
  · funext a c; by_cases ha : a = j
    · subst ha; simp [h]
    · simp [ha]

def pstep (m : BM n) (i : Fin n) : BM n := fun a c => m a c || (m a i && m i c)

def G2 (m0 : BM n) (i : Fin n) (S : List (Fin n)) : BM n :=
  fun a c => if a ∈ S then m0 a c || (m0 a i && m0 i c) else m0 a c

lemma jloop (m0 : BM n) (i : Fin n) :
    ∀ (l S : List (Fin n)), l.Nodup → (∀ x ∈ l, x ∉ S) →
      l.foldl (fun m j => rowS i j m) (G2 m0 i S) = G2 m0 i (l ++ S) := by
  intro l
  induction l with
  | nil => intro S _ _; simp
  | cons j l ih =>
    intro S hnd hdis
    rw [List.foldl_cons]
    have hj : j ∉ S := hdis j (by simp)
    have hstep : rowS i j (G2 m0 i S) = G2 m0 i (j :: S) := by
      rw [rowS_eq]
      funext a c
      by_cases ha : a = j
      · subst ha
        have hik : G2 m0 i S i c = m0 i c := by
          unfold G2; split_ifs <;> cases m0 i c <;> simp
        simp only [Function.update_self, hik]
        simp [G2, hj]
      · simp [G2, ha, Function.update_apply]
    rw [hstep, ih (j :: S) (List.nodup_cons.mp hnd).2 ?_]
    · have hm : ∀ x, x ∈ l ++ j :: S ↔ x ∈ j :: l ++ S := by
        intro x; simp only [List.mem_append, List.mem_cons]; tauto
      unfold G2; simp only [hm]
    · intro x hx hxS
      rcases List.mem_cons.mp hxS with h | h
      · subst h; exact (List.nodup_cons.mp hnd).1 hx
      · exact hdis x (by simp [hx]) h

lemma pivot_eq (m : BM n) (i : Fin n) :
    (List.finRange n).foldl (fun m j => rowS i j m) m = pstep m i := by
  have h0 : G2 m i [] = m := by funext a c; simp [G2]
  conv_lhs => rw [← h0]
  rw [jloop m i _ [] (List.nodup_finRange n) (by simp)]
  funext a c; simp [G2, pstep]

lemma alg_eq (b : BM n) :
    algorithm96 b = (List.finRange n).foldl pstep b := by
  unfold algorithm96
  have : (fun (m : BM n) (i : Fin n) => (List.finRange n).foldl (fun m j =>
      if m j i then
        (List.finRange n).foldl (fun m k =>
          if m i k then Function.update m j (Function.update (m j) k true)
          else m) m
      else m) m) = pstep := by
    funext m i
    rw [← pivot_eq]
    rfl
  rw [this]

def Closed (m : BM n) (u : Fin n) : Prop := ∀ a c, m a u = true → m u c = true → m a c = true

lemma pstep_closed_old (m : BM n) (u v : Fin n) (h : Closed m u) : Closed (pstep m v) u := by
  intro a c h1 h2
  simp only [pstep, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h a c h1 h2)
  · exact Or.inr ⟨h a v h1 h2, h2'⟩
  · exact Or.inr ⟨h1, h v c h1' h2⟩
  · exact Or.inr ⟨h1, h2'⟩

lemma pstep_closed_new (m : BM n) (v : Fin n) : Closed (pstep m v) v := by
  intro a c h1 h2
  simp only [pstep, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
  have h1' : m a v = true := by rcases h1 with h1 | h1 <;> [exact h1; exact h1.1]
  have h2' : m v c = true := by rcases h2 with h2 | h2 <;> [exact h2; exact h2.2]
  exact Or.inr ⟨h1', h2'⟩

lemma foldl_closed : ∀ (l : List (Fin n)) (m : BM n) (u : Fin n),
    (Closed m u ∨ u ∈ l) → Closed (l.foldl pstep m) u := by
  intro l
  induction l with
  | nil => intro m u h; simpa using h
  | cons v l ih =>
    intro m u h
    rw [List.foldl_cons]
    apply ih
    by_cases hv : u = v
    · subst hv; exact Or.inl (pstep_closed_new m u)
    · rcases h with h | h
      · exact Or.inl (pstep_closed_old m u v h)
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h hv
        · exact Or.inr h

lemma foldl_mono : ∀ (l : List (Fin n)) (m : BM n) (a c : Fin n),
    m a c = true → (l.foldl pstep m) a c = true := by
  intro l
  induction l with
  | nil => intro m a c h; simpa using h
  | cons v l ih =>
    intro m a c h
    rw [List.foldl_cons]
    apply ih
    simp [pstep, h]

lemma foldl_sound (R : Fin n → Fin n → Prop) (hR : Transitive R) : ∀ (l : List (Fin n)) (m : BM n),
    (∀ a c, m a c = true → R a c) → ∀ a c, (l.foldl pstep m) a c = true → R a c := by
  intro l
  induction l with
  | nil => intro m h; simpa using h
  | cons v l ih =>
    intro m h
    rw [List.foldl_cons]
    apply ih
    intro a c hac
    simp only [pstep, Bool.or_eq_true, Bool.and_eq_true] at hac
    rcases hac with hac | ⟨h1, h2⟩
    · exact h a c hac
    · exact hR (h a v h1) (h v c h2)

theorem a96_core (b : Fin n → Fin n → Bool) (i j : Fin n) :
    algorithm96 b i j = true ↔ Relation.TransGen (fun a c => b a c = true) i j := by
  rw [alg_eq]
  constructor
  · intro h
    exact foldl_sound (Relation.TransGen (fun a c => b a c = true)) (fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2) _ b
      (fun a c h => Relation.TransGen.single (r := fun a c => b a c = true) h) i j h
  · intro h
    induction h with
    | single h => exact foldl_mono _ b _ _ h
    | tail _ hbc ih =>
      exact foldl_closed _ b _ (Or.inr (List.mem_finRange _)) _ _ ih (foldl_mono _ b _ _ hbc)

end A96

end FloydAlgorithms.ShortestPath

open FloydAlgorithms.ShortestPath


theorem solution {n : ℕ} (b : Fin n → Fin n → Bool)
    (i j : Fin n) :
    algorithm96 b i j = true ↔ Relation.TransGen (fun a c => b a c = true) i j := by
  exact A96.a96_core b i j
