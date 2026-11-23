-- Prove2me | solution 1 for DynOracleConn.list_to_matrix
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:29:33.373248+00:00
-- url     : https://prove2.me/submissions/b59e00c2-bff7-40c7-aab8-a0c7b724d75e

import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_DetAlg

open DynOracleConn

namespace AuxListToMatrix

def queryVertex {n : ℕ} : ListQuery n → Fin n
  | .degree v => v
  | .neighbor v _ => v

def decodeListReply {n : ℕ} : ListQuery n → List (Fin n) → ℕ
  | .degree _, nbrs => nbrs.length
  | .neighbor _ j, nbrs =>
      if j = 0 then 0 else ((nbrs[j - 1]?).map (fun w => w.val + 1)).getD 0

def scanRow {n : ℕ} {R : Type} (v : Fin n) :
    List (Fin n) → (List (Fin n) → ProbeTree (Fin n × Fin n) Bool R) →
    ProbeTree (Fin n × Fin n) Bool R
  | [], cont => cont []
  | w :: ws, cont =>
      .probe (v, w) (fun b => scanRow v ws (fun rest => cont (if b then w :: rest else rest)))

lemma scanRow_run {n : ℕ} {R : Type} (v : Fin n) (ws : List (Fin n))
    (cont : List (Fin n) → ProbeTree (Fin n × Fin n) Bool R)
    (O : Fin n × Fin n → Bool) :
    (scanRow v ws cont).run O = (cont (ws.filter (fun w => O (v, w)))).run O := by
  induction ws generalizing cont with
  | nil => rfl
  | cons w ws ih =>
      simp only [scanRow, ProbeTree.run, List.filter_cons]
      rw [ih]

lemma scanRow_transcript {n : ℕ} {R : Type} (v : Fin n) (ws : List (Fin n))
    (cont : List (Fin n) → ProbeTree (Fin n × Fin n) Bool R)
    (O : Fin n × Fin n → Bool) :
    (scanRow v ws cont).transcript O =
      ws.map (fun w => ((v, w), O (v, w))) ++
        (cont (ws.filter (fun w => O (v, w)))).transcript O := by
  induction ws generalizing cont with
  | nil => rfl
  | cons w ws ih =>
      simp only [scanRow, ProbeTree.transcript, List.map_cons, List.cons_append, List.filter_cons]
      rw [ih]

lemma eq_of_pairwise_lt {α : Type} [LinearOrder α] :
    ∀ {l₁ l₂ : List α}, List.Pairwise (· < ·) l₁ → List.Pairwise (· < ·) l₂ →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | a :: _, [], _, _, hmem => nomatch (hmem a).mp List.mem_cons_self
  | [], b :: _, _, _, hmem => nomatch (hmem b).mpr List.mem_cons_self
  | a :: l₁, b :: l₂, hp₁, hp₂, hmem => by
      rw [List.pairwise_cons] at hp₁ hp₂
      have hab1 : a ∈ b :: l₂ := (hmem a).mp List.mem_cons_self
      have hab2 : b ∈ a :: l₁ := (hmem b).mpr List.mem_cons_self
      have hab : a = b := by
        rcases List.mem_cons.mp hab1 with rfl | ha₂
        · rfl
        · rcases List.mem_cons.mp hab2 with rfl | hb₁
          · rfl
          · exact False.elim (lt_asymm (hp₂.1 a ha₂) (hp₁.1 b hb₁))
      subst hab
      congr 1
      apply eq_of_pairwise_lt hp₁.2 hp₂.2
      intro x
      constructor
      · intro hx₁
        have hxne : x ≠ a := ne_of_gt (hp₁.1 x hx₁)
        exact List.mem_of_ne_of_mem hxne ((hmem x).mp (List.mem_cons_of_mem a hx₁))
      · intro hx₂
        have hxne : x ≠ a := ne_of_gt (hp₂.1 x hx₂)
        exact List.mem_of_ne_of_mem hxne ((hmem x).mpr (List.mem_cons_of_mem a hx₂))

lemma pairwise_lt_of_le_nodup {α : Type} [LinearOrder α] {l : List α}
    (hle : List.Pairwise (· ≤ ·) l) (hnodup : l.Nodup) : List.Pairwise (· < ·) l := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
      rw [List.pairwise_cons] at hle ⊢
      rw [List.nodup_cons] at hnodup
      refine ⟨fun b hb => lt_of_le_of_ne (hle.1 b hb) (fun h => hnodup.1 (h ▸ hb)),
        ih hle.2 hnodup.2⟩

lemma filter_finRange_eq_nbrList {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (List.finRange n).filter (fun w => matrixOracle G (v, w)) = nbrList G v := by
  apply eq_of_pairwise_lt
  · exact (List.pairwise_lt_finRange n).filter _
  · unfold nbrList
    exact pairwise_lt_of_le_nodup (Finset.pairwise_sort _ (· ≤ ·)) (Finset.sort_nodup _ (· ≤ ·))
  · intro w
    simp [nbrList, matrixOracle]

def simTree {n : ℕ} {R : Type} :
    ProbeTree (ListQuery n) ℕ R → ProbeTree (Fin n × Fin n) Bool R
  | .done r => .done r
  | .probe q k =>
      scanRow (queryVertex q) (List.finRange n)
        (fun nbrs => simTree (k (decodeListReply q nbrs)))

lemma decode_nbrList {n : ℕ} (G : SimpleGraph (Fin n)) (q : ListQuery n) :
    decodeListReply q (nbrList G (queryVertex q)) = listOracle G q := by
  cases q <;> rfl

lemma simTree_run {n : ℕ} {R : Type} (t : ProbeTree (ListQuery n) ℕ R) (G : SimpleGraph (Fin n)) :
    (simTree t).run (matrixOracle G) = t.run (listOracle G) := by
  induction t with
  | done r => rfl
  | probe q k ih =>
      simp only [simTree, scanRow_run, filter_finRange_eq_nbrList, decode_nbrList, ProbeTree.run]
      exact ih (listOracle G q)

lemma simTree_transcript {n : ℕ} {R : Type} (t : ProbeTree (ListQuery n) ℕ R)
    (G : SimpleGraph (Fin n)) :
    (simTree t).transcript (matrixOracle G) =
      (t.transcript (listOracle G)).flatMap (fun p =>
        (List.finRange n).map (fun w => ((queryVertex p.1, w), matrixOracle G (queryVertex p.1, w)))) := by
  induction t with
  | done r => rfl
  | probe q k ih =>
      simp only [simTree, scanRow_transcript, filter_finRange_eq_nbrList, decode_nbrList,
        ProbeTree.transcript, List.flatMap_cons]
      rw [ih (listOracle G q)]

def simAlg {n : ℕ} {S : Type} (A : DetAlg n (ListQuery n) ℕ S) :
    DetAlg n (Fin n × Fin n) Bool S where
  init := A.init
  step k st u := simTree (A.step k st u)

noncomputable def mapSteps {n : ℕ} :
    SimpleGraph (Fin n) → List (PunctSketch.Update n) →
    List (List (ListQuery n × ℕ) × Bool) → List (List ((Fin n × Fin n) × Bool) × Bool)
  | _, [], _ => []
  | _, _ :: _, [] => []
  | G, u :: rest, (qs, ans) :: trRest =>
      (qs.flatMap (fun p =>
        (List.finRange n).map (fun w => ((queryVertex p.1, w), matrixOracle G (queryVertex p.1, w)))),
       ans) :: mapSteps (u.apply G) rest trRest

lemma runFrom_simAlg {n : ℕ} {S : Type} (A : DetAlg n (ListQuery n) ℕ S) :
    ∀ (k : ℕ) (st : S) (G : SimpleGraph (Fin n)) (rest : List (PunctSketch.Update n)),
      (simAlg A).runFrom matrixOracle k st G rest =
        mapSteps G rest (A.runFrom listOracle k st G rest)
  | _, _, _, [] => rfl
  | k, st, G, u :: rest => by
      conv_lhs => unfold DetAlg.runFrom
      conv_rhs => unfold DetAlg.runFrom
      change ((simTree (A.step k st u)).transcript (matrixOracle G),
          ((simTree (A.step k st u)).run (matrixOracle G)).2) ::
          (simAlg A).runFrom matrixOracle (k + 1)
            ((simTree (A.step k st u)).run (matrixOracle G)).1 (u.apply G) rest = _
      rw [simTree_transcript, simTree_run, mapSteps, runFrom_simAlg A (k + 1) _ (u.apply G) rest]

lemma flatMap_row_length {n : ℕ} (G : SimpleGraph (Fin n)) (qs : List (ListQuery n × ℕ)) :
    (qs.flatMap (fun p =>
      (List.finRange n).map (fun w => ((queryVertex p.1, w), matrixOracle G (queryVertex p.1, w))))).length =
    n * qs.length := by
  induction qs with
  | nil => simp
  | cons p qs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_finRange,
        List.length_cons, ih]
      ring

lemma mapSteps_answers {n : ℕ} :
    ∀ (G : SimpleGraph (Fin n)) (rest : List (PunctSketch.Update n))
      (tr : List (List (ListQuery n × ℕ) × Bool)),
      tr.length = rest.length →
      (mapSteps G rest tr).map Prod.snd = tr.map Prod.snd
  | _, [], [], _ => rfl
  | G, u :: rest, (qs, ans) :: tr, hlen => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [mapSteps, List.map_cons]
      rw [mapSteps_answers (u.apply G) rest tr hlen]

lemma runFrom_length {n : ℕ} {Q Ans S : Type} (A : DetAlg n Q Ans S)
    (O : SimpleGraph (Fin n) → Q → Ans) :
    ∀ (k : ℕ) (st : S) (G : SimpleGraph (Fin n)) (rest : List (PunctSketch.Update n)),
      (A.runFrom O k st G rest).length = rest.length
  | _, _, _, [] => rfl
  | k, st, G, u :: rest => by
      simp [DetAlg.runFrom, runFrom_length A O (k + 1) _ (u.apply G) rest]

lemma mapSteps_cost {n : ℕ} :
    ∀ (G : SimpleGraph (Fin n)) (rest : List (PunctSketch.Update n))
      (tr : List (List (ListQuery n × ℕ) × Bool)),
      tr.length = rest.length →
      ((mapSteps G rest tr).map (fun p => p.1.length)).sum =
        n * (tr.map (fun p => p.1.length)).sum
  | _, [], [], _ => by simp [mapSteps]
  | G, u :: rest, (qs, ans) :: tr, hlen => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [mapSteps, List.map_cons, List.sum_cons, flatMap_row_length]
      rw [mapSteps_cost (u.apply G) rest tr hlen]
      ring

end AuxListToMatrix

theorem solution {n : ℕ} {S : Type} :
    ∃ sim : DetAlg n (ListQuery n) ℕ S → DetAlg n (Fin n × Fin n) Bool S,
      ∀ σ : List (PunctSketch.Update n),
        ∃ F : List (List (ListQuery n × ℕ) × Bool) → List (List ((Fin n × Fin n) × Bool) × Bool),
          ∀ A : DetAlg n (ListQuery n) ℕ S,
            (sim A).transcript matrixOracle σ = F (A.transcript listOracle σ) ∧
            (sim A).answers matrixOracle σ = A.answers listOracle σ ∧
            (sim A).totalCost matrixOracle σ ≤ n * A.totalCost listOracle σ := by
  refine ⟨AuxListToMatrix.simAlg, fun σ => ⟨AuxListToMatrix.mapSteps ⊥ σ, fun A => ?_⟩⟩
  have htr : (AuxListToMatrix.simAlg A).transcript matrixOracle σ =
      AuxListToMatrix.mapSteps ⊥ σ (A.transcript listOracle σ) :=
    AuxListToMatrix.runFrom_simAlg A 0 A.init ⊥ σ
  have hlen : (A.transcript listOracle σ).length = σ.length :=
    AuxListToMatrix.runFrom_length A listOracle 0 A.init ⊥ σ
  refine ⟨htr, ?_, ?_⟩
  · unfold DetAlg.answers
    rw [htr]
    exact AuxListToMatrix.mapSteps_answers ⊥ σ _ hlen
  · unfold DetAlg.totalCost
    rw [htr, AuxListToMatrix.mapSteps_cost ⊥ σ _ hlen]
