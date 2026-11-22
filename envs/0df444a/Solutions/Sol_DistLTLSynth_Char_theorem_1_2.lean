-- Prove2me | solution 1 for DistLTLSynth.Char.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:49:10.730773+00:00
-- url     : https://prove2.me/submissions/ece32b27-62f5-4b5a-93de-efa8e1cb3cfe

import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_CounterMachine
import Theorems.Thm_DistLTLSynth_Char_theorem_3_4
import Theorems.Thm_DistLTLSynth_Char_lemma_6_16
import Theorems.Thm_DistLTLSynth_Char_lemma_6_17
import Theorems.Thm_DistLTLSynth_Char_section_6_2_two_counter_reduction
import Theorems.Thm_DistLTLSynth_Char_section_3_2_minsky

namespace DistLTLSynth.Char.Thm12Aux
open DistLTLSynth.Char

/-! ### Part 1: Finite DPA encoding into `DPACode` -/

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
    | succ t ih =>
      simp only [DPA.run, ih, hstep]
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

/-! ### Part 2: Prefix-Polish serializer and `hatFormula` on `Instance` -/

def encFormula : Formula ℕ ℕ ℕ ℕ → List Token
  | .inp1 x => [(0, 1, x)]
  | .inp2 x => [(0, 2, x)]
  | .out1 y => [(1, 1, y)]
  | .out2 y => [(1, 2, y)]
  | .graph .oneToTwo => [(2, 0, 0)]
  | .graph .both => [(2, 1, 0)]
  | .graph .twoToOne => [(2, 2, 0)]
  | .next φ => (3, 0, 0) :: encFormula φ
  | .eventually φ => (4, 0, 0) :: encFormula φ
  | .always φ => (5, 0, 0) :: encFormula φ
  | .untl φ ψ => (6, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .weakUntil ψ φ => (7, 0, 0) :: (encFormula ψ ++ encFormula φ)
  | .neg φ => (8, 0, 0) :: encFormula φ
  | .or φ ψ => (9, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .and φ ψ => (10, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .imp φ ψ => (11, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .iff φ ψ => (12, 0, 0) :: (encFormula φ ++ encFormula ψ)

lemma parseAux_enc (φ : Formula ℕ ℕ ℕ ℕ) :
    ∀ (rest : List Token) (m : ℕ), (encFormula φ).length ≤ m →
      parseAux m (encFormula φ ++ rest) = some (φ, rest) := by
  induction φ with
  | inp1 x => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | inp2 x => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | out1 y => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | out2 y => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | graph g =>
    intro rest m hm
    cases g <;> (obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl)
  | next φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    simp [encFormula, parseAux, ih rest k hk]
  | eventually φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    simp [encFormula, parseAux, ih rest k hk]
  | always φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    simp [encFormula, parseAux, ih rest k hk]
  | neg φ ih =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    simp [encFormula, parseAux, ih rest k hk]
  | untl φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk1 : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    have hk2 : (encFormula ψ).length ≤ k := by simp [encFormula] at hm; omega
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k hk1]; dsimp only
    rw [ih2 rest k hk2]
  | weakUntil ψ φ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk1 : (encFormula ψ).length ≤ k := by simp [encFormula] at hm; omega
    have hk2 : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula φ ++ rest) k hk1]; dsimp only
    rw [ih2 rest k hk2]
  | or φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk1 : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    have hk2 : (encFormula ψ).length ≤ k := by simp [encFormula] at hm; omega
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k hk1]; dsimp only
    rw [ih2 rest k hk2]
  | and φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk1 : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    have hk2 : (encFormula ψ).length ≤ k := by simp [encFormula] at hm; omega
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k hk1]; dsimp only
    rw [ih2 rest k hk2]
  | imp φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk1 : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    have hk2 : (encFormula ψ).length ≤ k := by simp [encFormula] at hm; omega
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k hk1]; dsimp only
    rw [ih2 rest k hk2]
  | iff φ ψ ih1 ih2 =>
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    have hk1 : (encFormula φ).length ≤ k := by simp [encFormula] at hm; omega
    have hk2 : (encFormula ψ).length ≤ k := by simp [encFormula] at hm; omega
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k hk1]; dsimp only
    rw [ih2 rest k hk2]

lemma parseAux_mono :
    ∀ (n : ℕ) (ts : List Token) (φ : Formula ℕ ℕ ℕ ℕ) (r : List Token),
      parseAux n ts = some (φ, r) → ∀ m, n ≤ m → parseAux m ts = some (φ, r)
  | 0, _, _, _, h => by simp [parseAux] at h
  | n + 1, [], _, _, h => by simp [parseAux] at h
  | n + 1, (tag, a, b) :: ts, φ, r, h => by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hnk : n ≤ k := by omega
    by_cases ht0 : tag = 0
    · subst ht0
      cases a with
      | zero => simp [parseAux] at h
      | succ a1 =>
        cases a1 with
        | zero => simpa [parseAux] using h
        | succ a2 =>
          cases a2 with
          | zero => simpa [parseAux] using h
          | succ _ => simp [parseAux] at h
    · by_cases ht1 : tag = 1
      · subst ht1
        cases a with
        | zero => simp [parseAux] at h
        | succ a1 =>
          cases a1 with
          | zero => simpa [parseAux] using h
          | succ a2 =>
            cases a2 with
            | zero => simpa [parseAux] using h
            | succ _ => simp [parseAux] at h
      · by_cases ht2 : tag = 2
        · subst ht2
          cases a with
          | zero => simpa [parseAux] using h
          | succ a1 =>
            cases a1 with
            | zero => simpa [parseAux] using h
            | succ a2 =>
              cases a2 with
              | zero => simpa [parseAux] using h
              | succ _ => simp [parseAux] at h
        · rcases (show tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 ∨
              tag = 9 ∨ tag = 10 ∨ tag = 11 ∨ tag = 12 ∨ 13 ≤ tag by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
          · simp only [parseAux] at h ⊢
            cases hp : parseAux n ts with
            | none => simp [hp] at h
            | some pr => rw [parseAux_mono n ts pr.1 pr.2 hp k hnk]; simpa [hp] using h
          · simp only [parseAux] at h ⊢
            cases hp : parseAux n ts with
            | none => simp [hp] at h
            | some pr => rw [parseAux_mono n ts pr.1 pr.2 hp k hnk]; simpa [hp] using h
          · simp only [parseAux] at h ⊢
            cases hp : parseAux n ts with
            | none => simp [hp] at h
            | some pr => rw [parseAux_mono n ts pr.1 pr.2 hp k hnk]; simpa [hp] using h
          · simp only [parseAux] at h ⊢
            cases hp1 : parseAux n ts with
            | none => simp [hp1] at h
            | some pr1 =>
              rw [parseAux_mono n ts pr1.1 pr1.2 hp1 k hnk]; dsimp only
              cases hp2 : parseAux n pr1.2 with
              | none => simp [hp1, hp2] at h
              | some pr2 =>
                rw [parseAux_mono n pr1.2 pr2.1 pr2.2 hp2 k hnk]
                simpa [hp1, hp2] using h
          · simp only [parseAux] at h ⊢
            cases hp1 : parseAux n ts with
            | none => simp [hp1] at h
            | some pr1 =>
              rw [parseAux_mono n ts pr1.1 pr1.2 hp1 k hnk]; dsimp only
              cases hp2 : parseAux n pr1.2 with
              | none => simp [hp1, hp2] at h
              | some pr2 =>
                rw [parseAux_mono n pr1.2 pr2.1 pr2.2 hp2 k hnk]
                simpa [hp1, hp2] using h
          · simp only [parseAux] at h ⊢
            cases hp : parseAux n ts with
            | none => simp [hp] at h
            | some pr => rw [parseAux_mono n ts pr.1 pr.2 hp k hnk]; simpa [hp] using h
          · simp only [parseAux] at h ⊢
            cases hp1 : parseAux n ts with
            | none => simp [hp1] at h
            | some pr1 =>
              rw [parseAux_mono n ts pr1.1 pr1.2 hp1 k hnk]; dsimp only
              cases hp2 : parseAux n pr1.2 with
              | none => simp [hp1, hp2] at h
              | some pr2 =>
                rw [parseAux_mono n pr1.2 pr2.1 pr2.2 hp2 k hnk]
                simpa [hp1, hp2] using h
          · simp only [parseAux] at h ⊢
            cases hp1 : parseAux n ts with
            | none => simp [hp1] at h
            | some pr1 =>
              rw [parseAux_mono n ts pr1.1 pr1.2 hp1 k hnk]; dsimp only
              cases hp2 : parseAux n pr1.2 with
              | none => simp [hp1, hp2] at h
              | some pr2 =>
                rw [parseAux_mono n pr1.2 pr2.1 pr2.2 hp2 k hnk]
                simpa [hp1, hp2] using h
          · simp only [parseAux] at h ⊢
            cases hp1 : parseAux n ts with
            | none => simp [hp1] at h
            | some pr1 =>
              rw [parseAux_mono n ts pr1.1 pr1.2 hp1 k hnk]; dsimp only
              cases hp2 : parseAux n pr1.2 with
              | none => simp [hp1, hp2] at h
              | some pr2 =>
                rw [parseAux_mono n pr1.2 pr2.1 pr2.2 hp2 k hnk]
                simpa [hp1, hp2] using h
          · simp only [parseAux] at h ⊢
            cases hp1 : parseAux n ts with
            | none => simp [hp1] at h
            | some pr1 =>
              rw [parseAux_mono n ts pr1.1 pr1.2 hp1 k hnk]; dsimp only
              cases hp2 : parseAux n pr1.2 with
              | none => simp [hp1, hp2] at h
              | some pr2 =>
                rw [parseAux_mono n pr1.2 pr2.1 pr2.2 hp2 k hnk]
                simpa [hp1, hp2] using h
          · obtain ⟨d, rfl⟩ : ∃ d, tag = d + 13 := ⟨tag - 13, by omega⟩
            simp [parseAux] at h

lemma parseAux_replicate_next (k : ℕ) (ts : List Token) (φ : Formula ℕ ℕ ℕ ℕ)
    (hts : parseAux ts.length ts = some (φ, [])) :
    parseAux (k + ts.length) (List.replicate k (3, 0, 0) ++ ts) =
      some (Formula.nextIter k φ, []) := by
  induction k with
  | zero => simpa [Formula.nextIter] using hts
  | succ k ih =>
    have hm : k + 1 + ts.length = (k + ts.length) + 1 := by omega
    rw [hm, List.replicate_succ, List.cons_append]
    simp [parseAux, Formula.nextIter, ih]

def hatHeader (h : List CommGraph) : List Token :=
  (11, 0, 0) :: (encFormula (prefixFormula h : Formula ℕ ℕ ℕ ℕ) ++ List.replicate h.length (3, 0, 0))

lemma parse_hatHeader (h : List CommGraph) (ts : List Token) (φ : Formula ℕ ℕ ℕ ℕ)
    (hp : parse ts = some φ) :
    parse (hatHeader h ++ ts) = some (hatFormula h φ) := by
  have hts : parseAux ts.length ts = some (φ, []) := by
    unfold parse at hp
    cases haux : parseAux ts.length ts with
    | none => simp [haux] at hp
    | some pr =>
      rcases pr with ⟨ψ, rem⟩
      cases rem with
      | nil =>
        simp [haux] at hp
        subst hp
        rfl
      | cons _ _ => simp [haux] at hp
  unfold parse hatHeader
  simp only [List.cons_append, List.append_assoc, List.length_cons, List.length_append,
    List.length_replicate]
  set k := (encFormula (prefixFormula h : Formula ℕ ℕ ℕ ℕ)).length + (h.length + ts.length)
  have h1 := parseAux_enc (prefixFormula h : Formula ℕ ℕ ℕ ℕ)
    (List.replicate h.length (3, 0, 0) ++ ts) k (by omega)
  have h2 := parseAux_mono (h.length + ts.length) (List.replicate h.length (3, 0, 0) ++ ts)
    (Formula.nextIter h.length φ) [] (parseAux_replicate_next h.length ts φ hts) k (by omega)
  dsimp only [parseAux]
  rw [h1]; dsimp only
  rw [h2]
  rfl

def hatInst (h : List CommGraph) (I : Instance) : Instance :=
  ⟨I.k1, I.k2, I.m1, I.m2, hatHeader h ++ I.tokens⟩

lemma primrec_prepend_tokens : ∀ (L : List Token), Primrec (fun ts : List Token => L ++ ts)
  | [] => by change Primrec id; exact Primrec.id
  | a :: L => Primrec.list_cons.comp (Primrec.const a) (primrec_prepend_tokens L)

lemma computable_hatInst (h : List CommGraph) : Computable (hatInst h) := by
  let tupMap : ℕ × ℕ × ℕ × ℕ × List Token → ℕ × ℕ × ℕ × ℕ × List Token :=
    fun t => (t.1, t.2.1, t.2.2.1, t.2.2.2.1, hatHeader h ++ t.2.2.2.2)
  have htup : Primrec tupMap :=
    Primrec.pair Primrec.fst
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            ((primrec_prepend_tokens (hatHeader h)).comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))))
  have henc : Primrec Instance.equiv.toFun := Primrec.of_equiv
  have hdec : Primrec Instance.equiv.invFun := Primrec.of_equiv_symm
  exact (hdec.comp (htup.comp henc)).to_comp

/-! ### Part 3: Bridging singleton `Instance` (`Fin 1`) and `Unit` formulas -/

def toUnitFormula (I : Instance) : Formula ℕ ℕ ℕ ℕ → Formula Unit Unit I.Y1 I.Y2
  | .inp1 x => if x = 0 then Formula.tt else Formula.ff
  | .inp2 x => if x = 0 then Formula.tt else Formula.ff
  | .out1 y => if hy : y < I.m1 + 1 then .out1 ⟨y, hy⟩ else Formula.ff
  | .out2 y => if hy : y < I.m2 + 1 then .out2 ⟨y, hy⟩ else Formula.ff
  | .graph g => .graph g
  | .next φ => .next (toUnitFormula I φ)
  | .eventually φ => .eventually (toUnitFormula I φ)
  | .always φ => .always (toUnitFormula I φ)
  | .untl φ ψ => .untl (toUnitFormula I φ) (toUnitFormula I ψ)
  | .weakUntil ψ φ => .weakUntil (toUnitFormula I ψ) (toUnitFormula I φ)
  | .neg φ => .neg (toUnitFormula I φ)
  | .or φ ψ => .or (toUnitFormula I φ) (toUnitFormula I ψ)
  | .and φ ψ => .and (toUnitFormula I φ) (toUnitFormula I ψ)
  | .imp φ ψ => .imp (toUnitFormula I φ) (toUnitFormula I ψ)
  | .iff φ ψ => .iff (toUnitFormula I φ) (toUnitFormula I ψ)

lemma toUnitFormula_hatInst (h : List CommGraph) (I : Instance) (ψ : Formula ℕ ℕ ℕ ℕ) :
    toUnitFormula (hatInst h I) ψ = toUnitFormula I ψ := by
  induction ψ <;> (simp [toUnitFormula, *]; rfl)

def unitToInstExec (I : Instance) (e : ℕ → Signal Unit Unit × (I.Y1 × I.Y2)) :
    ℕ → Signal I.X1 I.X2 × (I.Y1 × I.Y2) :=
  fun n => ((⟨0, Nat.succ_pos _⟩, ⟨0, Nat.succ_pos _⟩, (e n).1.2.2), (e n).2)

def instToUnitExec (I : Instance) (e : ℕ → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :
    ℕ → Signal Unit Unit × (I.Y1 × I.Y2) :=
  fun n => (((), (), (e n).1.2.2), (e n).2)

lemma sat_tt_any {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.tt : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.tt, Formula.Sat]
  exact em _

lemma sat_ff_any {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    ¬ (Formula.ff : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.ff, Formula.Sat]
  exact not_not_intro (sat_tt_any e)

lemma shift_valExec_unit (I : Instance) (e : ℕ → Signal Unit Unit × (I.Y1 × I.Y2)) (r : ℕ) :
    shift (valExec (unitToInstExec I e)) r = valExec (unitToInstExec I (shift e r)) := rfl

lemma sat_toUnitFormula (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ) :
    ∀ e : ℕ → Signal Unit Unit × (I.Y1 × I.Y2),
      (toUnitFormula I φ).Sat e ↔ φ.Sat (valExec (unitToInstExec I e)) := by
  induction φ with
  | inp1 x =>
    intro e; simp only [toUnitFormula, Formula.Sat, valExec, unitToInstExec]
    by_cases hx : x = 0
    · subst hx; simp [sat_tt_any]
    · simp [hx, sat_ff_any, Ne.symm hx]
  | inp2 x =>
    intro e; simp only [toUnitFormula, Formula.Sat, valExec, unitToInstExec]
    by_cases hx : x = 0
    · subst hx; simp [sat_tt_any]
    · simp [hx, sat_ff_any, Ne.symm hx]
  | out1 y =>
    intro e; simp only [toUnitFormula, Formula.Sat, valExec, unitToInstExec]
    by_cases hy : y < I.m1 + 1
    · rw [dif_pos hy]
      simp only [Formula.Sat]
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    · rw [dif_neg hy]
      refine ⟨fun h => absurd h (sat_ff_any e), fun h => absurd (h ▸ (e 0).2.1.isLt) hy⟩
  | out2 y =>
    intro e; simp only [toUnitFormula, Formula.Sat, valExec, unitToInstExec]
    by_cases hy : y < I.m2 + 1
    · rw [dif_pos hy]
      simp only [Formula.Sat]
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    · rw [dif_neg hy]
      refine ⟨fun h => absurd h (sat_ff_any e), fun h => absurd (h ▸ (e 0).2.2.isLt) hy⟩
  | graph g => intro e; rfl
  | next φ ih => intro e; simp [toUnitFormula, Formula.Sat, ih, shift_valExec_unit]
  | eventually φ ih => intro e; simp [toUnitFormula, Formula.Sat, ih, shift_valExec_unit]
  | always φ ih => intro e; simp [toUnitFormula, Formula.Sat, ih, shift_valExec_unit]
  | untl φ ψ ih1 ih2 => intro e; simp [toUnitFormula, Formula.Sat, ih1, ih2, shift_valExec_unit]
  | weakUntil ψ φ ih1 ih2 => intro e; simp [toUnitFormula, Formula.Sat, ih1, ih2, shift_valExec_unit]
  | neg φ ih => intro e; simp [toUnitFormula, Formula.Sat, ih]
  | or φ ψ ih1 ih2 => intro e; simp [toUnitFormula, Formula.Sat, ih1, ih2]
  | and φ ψ ih1 ih2 => intro e; simp [toUnitFormula, Formula.Sat, ih1, ih2]
  | imp φ ψ ih1 ih2 => intro e; simp [toUnitFormula, Formula.Sat, ih1, ih2]
  | iff φ ψ ih1 ih2 => intro e; simp [toUnitFormula, Formula.Sat, ih1, ih2]

lemma toUnitFormula_bigAnd (I : Instance) (l : List (Formula ℕ ℕ ℕ ℕ)) :
    toUnitFormula I (Formula.bigAnd l) = Formula.bigAnd (l.map (toUnitFormula I)) := by
  induction l with
  | nil => rfl
  | cons a tl ih => simp [Formula.bigAnd, toUnitFormula, ih]

lemma toUnitFormula_nextIter (I : Instance) (k : ℕ) (φ : Formula ℕ ℕ ℕ ℕ) :
    toUnitFormula I (Formula.nextIter k φ) = Formula.nextIter k (toUnitFormula I φ) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Formula.nextIter, toUnitFormula, ih]

lemma toUnitFormula_hatFormula (I : Instance) (h : List CommGraph) (φ : Formula ℕ ℕ ℕ ℕ) :
    toUnitFormula I (hatFormula h φ) = hatFormula h (toUnitFormula I φ) := by
  simp only [hatFormula, prefixFormula, toUnitFormula, toUnitFormula_bigAnd,
    toUnitFormula_nextIter, List.map_map]
  congr 2
  apply List.map_congr_left
  intro i _
  simp [Function.comp, toUnitFormula_nextIter, toUnitFormula]

def viewToUnit {X1 X2 : Type} : View X1 X2 → View Unit Unit
  | .I1 => .I1
  | .I2 => .I2
  | .N1 _ u => .N1 () (viewToUnit u)
  | .N2 _ v => .N2 () (viewToUnit v)
  | .C1 _ u _ v => .C1 () (viewToUnit u) () (viewToUnit v)
  | .C2 _ v _ u => .C2 () (viewToUnit v) () (viewToUnit u)

def viewFromUnit (I : Instance) : View Unit Unit → View I.X1 I.X2
  | .I1 => .I1
  | .I2 => .I2
  | .N1 _ u => .N1 ⟨0, Nat.succ_pos _⟩ (viewFromUnit I u)
  | .N2 _ v => .N2 ⟨0, Nat.succ_pos _⟩ (viewFromUnit I v)
  | .C1 _ u _ v => .C1 ⟨0, Nat.succ_pos _⟩ (viewFromUnit I u) ⟨0, Nat.succ_pos _⟩ (viewFromUnit I v)
  | .C2 _ v _ u => .C2 ⟨0, Nat.succ_pos _⟩ (viewFromUnit I v) ⟨0, Nat.succ_pos _⟩ (viewFromUnit I u)

lemma views_append_one {X1 X2 : Type} (l : List (Signal X1 X2)) (a : Signal X1 X2) :
    views (l ++ [a]) = viewStep (views l) a := by simp [views]

lemma viewToUnit_views {X1 X2 : Type} (l : List (Signal X1 X2)) :
    viewToUnit (view1 l) = view1 (l.map fun s => ((), (), s.2.2)) ∧
      viewToUnit (view2 l) = view2 (l.map fun s => ((), (), s.2.2)) := by
  induction l using List.reverseRecOn with
  | nil => simp [view1, view2, views, viewToUnit]
  | append_singleton l a ih =>
    rcases a with ⟨x1, x2, g⟩
    unfold view1 view2 at ih ⊢
    simp only [List.map_append, List.map_singleton]
    rw [views_append_one, views_append_one]
    cases g <;> simp [viewStep, viewToUnit, ih.1, ih.2]

lemma viewFromUnit_views (I : Instance) (l : List (Signal Unit Unit)) :
    viewFromUnit I (view1 l) = view1 (l.map fun s => (⟨0, Nat.succ_pos _⟩, ⟨0, Nat.succ_pos _⟩, s.2.2)) ∧
      viewFromUnit I (view2 l) = view2 (l.map fun s => (⟨0, Nat.succ_pos _⟩, ⟨0, Nat.succ_pos _⟩, s.2.2)) := by
  induction l using List.reverseRecOn with
  | nil => simp [view1, view2, views, viewFromUnit]
  | append_singleton l a ih =>
    rcases a with ⟨⟨⟩, ⟨⟩, g⟩
    unfold view1 view2 at ih ⊢
    simp only [List.map_append, List.map_singleton]
    rw [views_append_one, views_append_one]
    cases g <;> simp [viewStep, viewFromUnit, ih.1, ih.2]

lemma inst_realizes_iff_unit (I : Instance) (hk1 : I.k1 = 0) (hk2 : I.k2 = 0)
    (B : Set (ℕ → CommGraph)) (φ : Formula ℕ ℕ ℕ ℕ) :
    (∃ f : Algorithm I.X1 I.X2 I.Y1 I.Y2, RealizesLang f B (I.Lang φ)) ↔
      Realizable B (toUnitFormula I φ) := by
  constructor
  · rintro ⟨f, hf⟩
    let fU : Algorithm Unit Unit I.Y1 I.Y2 :=
      ⟨fun v => f.f1 (viewFromUnit I v), fun v => f.f2 (viewFromUnit I v)⟩
    refine ⟨fU, fun s hs => ?_⟩
    change (toUnitFormula I φ).Sat (exec fU s)
    rw [sat_toUnitFormula]
    let sI : ℕ → Signal I.X1 I.X2 := fun n => (⟨0, Nat.succ_pos _⟩, ⟨0, Nat.succ_pos _⟩, (s n).2.2)
    have hgI : graphOf sI ∈ B := hs
    have hsatI : φ.Sat (valExec (exec f sI)) := hf sI hgI
    have hexec : unitToInstExec I (exec fU s) = exec f sI := by
      funext n
      have hpre : (pre s (n + 1)).map (fun a => (⟨0, Nat.succ_pos _⟩, ⟨0, Nat.succ_pos _⟩, a.2.2)) =
          pre sI (n + 1) := by
        apply List.ext_getElem
        · simp [pre]
        · intro i h1 h2
          simp only [pre, List.getElem_map, List.getElem_ofFn, sI]
      have hv := viewFromUnit_views I (pre s (n + 1))
      rw [hpre] at hv
      simp [unitToInstExec, exec, fU, sI, hv.1, hv.2]
    rwa [hexec]
  · rintro ⟨fU, hfU⟩
    let f : Algorithm I.X1 I.X2 I.Y1 I.Y2 :=
      ⟨fun v => fU.f1 (viewToUnit v), fun v => fU.f2 (viewToUnit v)⟩
    refine ⟨f, fun sI hsI => ?_⟩
    let s : ℕ → Signal Unit Unit := fun n => ((), (), (sI n).2.2)
    have hsatU : (toUnitFormula I φ).Sat (exec fU s) := hfU s hsI
    rw [sat_toUnitFormula] at hsatU
    have hexec : unitToInstExec I (exec fU s) = exec f sI := by
      funext n
      have hpre : (pre sI (n + 1)).map (fun a => ((), (), a.2.2)) = pre s (n + 1) := by
        apply List.ext_getElem
        · simp [pre]
        · intro i h1 h2
          simp only [pre, List.getElem_map, List.getElem_ofFn, s]
      have hv := viewToUnit_views (pre sI (n + 1))
      rw [hpre] at hv
      rcases hsIn : sI n with ⟨x1, x2, g⟩
      have hx1 : x1 = ⟨0, Nat.succ_pos _⟩ := by apply Fin.ext; have := x1.isLt; omega
      have hx2 : x2 = ⟨0, Nat.succ_pos _⟩ := by apply Fin.ext; have := x2.isLt; omega
      subst hx1 hx2
      simp [unitToInstExec, exec, f, s, hsIn, hv.1, hv.2]
    change φ.Sat (valExec (exec f sI))
    rwa [← hexec]

lemma append_pre_lt_aux {α : Type} (x u : ℕ → α) (m k : ℕ) (hk : k < m) :
    append (pre x m) u k = x k := by
  unfold append
  have hlt : k < (pre x m).length := by simp [pre, hk]
  rw [dif_pos hlt]
  simp only [pre, List.getElem_ofFn]

lemma append_pre_ge_aux {α : Type} (x u : ℕ → α) (m k : ℕ) (hk : ¬ (k < m)) :
    append (pre x m) u k = u (k - m) := by
  unfold append
  have hl : (pre x m).length = m := by simp [pre]
  have hlt : ¬ (k < (pre x m).length) := by rw [hl]; exact hk
  rw [dif_neg hlt, hl]

lemma toUnitFormula_isSafety (I : Instance)
    (φ : Formula ℕ ℕ ℕ ℕ) (hsaf : DistLTLSynth.Char.IsSafety (I.Lang φ)) :
    (toUnitFormula I φ).IsSafety := by
  intro t ht
  have ht' : ¬ φ.Sat (valExec (unitToInstExec I t)) :=
    fun h => ht ((sat_toUnitFormula I φ t).mpr h)
  obtain ⟨i, hi⟩ := hsaf (unitToInstExec I t) ht'
  refine ⟨i, fun u hu => ?_⟩
  have hu' : φ.Sat (valExec (unitToInstExec I (append (pre t i) u))) :=
    (sat_toUnitFormula I φ _).mp hu
  have happ : unitToInstExec I (append (pre t i) u) =
      append (pre (unitToInstExec I t) i) (unitToInstExec I u) := by
    funext n
    by_cases hn : n < i
    · rw [append_pre_lt_aux _ _ i n hn]
      unfold unitToInstExec
      rw [append_pre_lt_aux t u i n hn]
    · rw [append_pre_ge_aux _ _ i n hn]
      unfold unitToInstExec
      rw [append_pre_ge_aux t u i n hn]
  rw [happ] at hu'
  exact hi (unitToInstExec I u) hu'

end DistLTLSynth.Char.Thm12Aux

open DistLTLSynth.Char DistLTLSynth.Char.Thm12Aux in
theorem solution {S : Type} [Fintype S] (M : DPA S CommGraph) :
    ComputablePred (fun I : Instance => I.Realizable M.lang) ↔
      IsNowhereDense (piMap '' M.lang) := by
  constructor
  · intro hcomp
    by_contra hnotND
    obtain ⟨h, hdense⟩ := lemma_6_16 M.lang hnotND
    obtain ⟨red, hred_comp, hred_spec⟩ := section_6_2_two_counter_reduction
    obtain ⟨g, hg_comp, hg_spec⟩ := ComputablePred.computable_iff.mp hcomp
    apply section_3_2_minsky
    refine ComputablePred.computable_iff.mpr
      ⟨fun m => !(g (hatInst h (red m))),
       Primrec.not.to_comp.comp (hg_comp.comp ((computable_hatInst h).comp hred_comp)), ?_⟩
    funext m
    apply propext
    obtain ⟨hk1, hk2, ⟨φ, hparse, hsaf⟩, hreal_iff⟩ := hred_spec m
    have hparse_hat : parse (hatInst h (red m)).tokens = some (hatFormula h φ) :=
      parse_hatHeader h (red m).tokens φ hparse
    have hhat_real_iff : (hatInst h (red m)).Realizable M.lang ↔ (red m).Realizable Set.univ := by
      have hU_saf : (toUnitFormula (red m) φ).IsSafety :=
        toUnitFormula_isSafety (red m) φ hsaf
      have h617 := @lemma_6_17 (red m).Y1 (red m).Y2 inferInstance ⟨⟨0, Nat.succ_pos _⟩⟩
        inferInstance ⟨⟨0, Nat.succ_pos _⟩⟩ M.lang h hdense (toUnitFormula (red m) φ) hU_saf
      have h1 : (red m).Realizable Set.univ ↔ Realizable Set.univ (toUnitFormula (red m) φ) := by
        constructor
        · rintro ⟨ψ, hψ, hf⟩
          have heq : ψ = φ := Option.some.inj (hψ.symm.trans hparse)
          subst ψ
          exact (inst_realizes_iff_unit (red m) hk1 hk2 Set.univ φ).mp hf
        · intro hU
          exact ⟨φ, hparse, (inst_realizes_iff_unit (red m) hk1 hk2 Set.univ φ).mpr hU⟩
      have h2 : (hatInst h (red m)).Realizable M.lang ↔
          Realizable M.lang (hatFormula h (toUnitFormula (red m) φ)) := by
        have hk1' : (hatInst h (red m)).k1 = 0 := hk1
        have hk2' : (hatInst h (red m)).k2 = 0 := hk2
        have htr := inst_realizes_iff_unit (hatInst h (red m)) hk1' hk2' M.lang (hatFormula h φ)
        have hsame : toUnitFormula (hatInst h (red m)) (hatFormula h φ) =
            hatFormula h (toUnitFormula (red m) φ) :=
          (toUnitFormula_hatInst h (red m) (hatFormula h φ)).trans
            (toUnitFormula_hatFormula (red m) h φ)
        constructor
        · rintro ⟨ψ, hψ, hf⟩
          have heq : ψ = hatFormula h φ := Option.some.inj (hψ.symm.trans hparse_hat)
          subst ψ
          exact hsame ▸ htr.mp hf
        · intro hU
          exact ⟨hatFormula h φ, hparse_hat, htr.mpr (hsame.symm ▸ hU)⟩
      exact h2.trans (h617.symm.trans h1.symm)
    have hg_at := congrFun hg_spec (hatInst h (red m))
    simp only [Bool.not_eq_true']
    constructor
    · intro hhalts
      by_contra htrue
      have hrealM : (hatInst h (red m)).Realizable M.lang := by
        rw [hg_at]; exact Bool.eq_true_of_not_eq_false htrue
      exact (hreal_iff.mp (hhat_real_iff.mp hrealM)) hhalts
    · intro hfalse
      have hnotM : ¬ (hatInst h (red m)).Realizable M.lang := by
        rw [hg_at, hfalse]; decide
      by_contra hnotHalts
      exact hnotM (hhat_real_iff.mpr (hreal_iff.mpr hnotHalts))
  · intro hND
    obtain ⟨c, hc_lang⟩ := exists_dpaCode M
    obtain ⟨dec, hdec_comp, _, _, hspec⟩ := theorem_3_4
    refine ComputablePred.computable_iff.mpr
      ⟨fun I => dec (c, I),
       hdec_comp.comp ((Computable.const c).pair Computable.id), ?_⟩
    funext I
    apply propext
    have hND_c : IsNowhereDense (piMap '' c.lang) := hc_lang ▸ hND
    rw [← hc_lang]
    exact ((hspec c I hND_c).1).symm
