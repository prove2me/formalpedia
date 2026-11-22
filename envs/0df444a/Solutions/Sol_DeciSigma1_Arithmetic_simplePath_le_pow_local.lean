-- Prove2me | solution 1 for DeciSigma1.Arithmetic.simplePath_le_pow_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:21.878833+00:00
-- url     : https://prove2.me/submissions/a7b60b8c-84eb-4a57-830c-f8902571f228

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Theorems.Thm_DeciSigma1_Arithmetic_isChain_forall_of_exists
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Arithmetic
variable {β : Type*}
private theorem exists_minimal_mem (r : β → β → Prop) [IsStrictOrder β r] {p : List β}
    (hne : p ≠ []) : ∃ m ∈ p, ∀ y ∈ p, ¬ r y m := by
  classical
  have hnon : p.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil p hne
    exact ⟨a, List.mem_toFinset.mpr ha⟩
  obtain ⟨m, hm, hmin⟩ := p.toFinset.exists_min_image
    (fun x => (p.toFinset.filter (fun y => r y x)).card) hnon
  refine ⟨m, List.mem_toFinset.mp hm, fun y hy hym => ?_⟩
  have hle := hmin y (List.mem_toFinset.mpr hy)
  have hsub : p.toFinset.filter (fun z => r z y) ⊂ p.toFinset.filter (fun z => r z m) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨y, ?_, ?_⟩
      · simp only [Finset.mem_filter, List.mem_toFinset]; exact ⟨hy, hym⟩
      · simp only [Finset.mem_filter, List.mem_toFinset, not_and]
        exact fun _ => irrefl_of r y
    · intro z
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact fun ⟨hz, hzy⟩ => ⟨hz, trans_of r hzy hym⟩
  exact absurd (Finset.card_lt_card hsub) (not_lt.mpr hle)
section Runs
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
end Runs
end DeciSigma1.Arithmetic
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
namespace DeciSigma1.Arithmetic
theorem _root_.solution (r : β → β → Prop) [IsStrictOrder β r] (H : ℕ) :
    ∀ (p : List β), p.Nodup → p.IsChain (fun x y => r x y ∨ r y x) →
      (∀ x ∈ p, ∀ y ∈ p, ∀ z ∈ p, r y x → r z x → y = z ∨ r y z ∨ r z y) →
      (∀ c : Finset β, (∀ x ∈ c, x ∈ p) → IsChain r (c : Set β) → c.card ≤ H) →
      p.length ≤ 2 ^ H - 1 := by
  classical
  induction H with
  | zero =>
    intro p _ _ _ hH
    cases p with
    | nil => simp
    | cons a l =>
      exfalso
      have := hH {a} (by simp) (by simp)
      simp at this
  | succ H ih =>
    intro p hnd hp hf hH
    rcases eq_or_ne p [] with rfl | hne
    · simp
    obtain ⟨m, hm, hmin⟩ := exists_minimal_mem r hne
    -- every vertex of the path lies above `m`
    have hstep : ∀ x ∈ p, ∀ y ∈ p, (r x y ∨ r y x) → (x = m ∨ r m x) → (y = m ∨ r m y) := by
      intro x hx y hy hxy hQx
      rcases hxy with hxy | hyx
      · right
        rcases hQx with rfl | hmx
        · exact hxy
        · exact trans_of r hmx hxy
      · rcases hQx with rfl | hmx
        · exact absurd hyx (hmin y hy)
        · rcases hf x hx m hm y hy hmx hyx with h | h | h
          · exact Or.inl h.symm
          · exact Or.inr h
          · exact absurd h (hmin y hy)
    have habove : ∀ x ∈ p, x = m ∨ r m x :=
      isChain_forall_of_exists hp
        (fun x hx y hy hxy => ⟨hstep x hx y hy hxy, hstep y hy x hx hxy.symm⟩)
        ⟨m, hm, Or.inl rfl⟩
    -- split the path at `m`
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hm
    have hnd' := List.nodup_middle.mp hnd
    rw [List.nodup_cons, List.mem_append, not_or] at hnd'
    obtain ⟨⟨hms, hmt⟩, hst⟩ := hnd'
    have hs_nd : s.Nodup := (List.nodup_append.mp hst).1
    have ht_nd : t.Nodup := (List.nodup_append.mp hst).2.1
    have hsplit := List.isChain_split.mp hp
    have hs_ch : s.IsChain (fun x y => r x y ∨ r y x) := (List.isChain_append.mp hsplit.1).1
    have ht_ch : t.IsChain (fun x y => r x y ∨ r y x) := hsplit.2.tail
    -- the induction hypothesis applies to each side
    have hside : ∀ q : List β, (∀ x ∈ q, x ∈ s ++ m :: t) → m ∉ q → q.Nodup →
        q.IsChain (fun x y => r x y ∨ r y x) → q.length ≤ 2 ^ H - 1 := by
      intro q hq hmq hqnd hqch
      refine ih q hqnd hqch (fun x hx y hy z hz => hf x (hq x hx) y (hq y hy) z (hq z hz)) ?_
      intro c hc hch
      have hmc : m ∉ c := fun h => hmq (hc m h)
      have hins : IsChain r ((insert m c : Finset β) : Set β) := by
        rw [Finset.coe_insert]
        refine hch.insert fun b hb hne => ?_
        rcases habove b (hq b (hc b hb)) with h | h
        · exact absurd h.symm hne
        · exact Or.inl h
      have := hH (insert m c) (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hm
        · exact hq x (hc x hx)) hins
      rw [Finset.card_insert_of_notMem hmc] at this
      omega
    have h1 := hside s (fun x hx => List.mem_append_left _ hx) hms hs_nd hs_ch
    have h2 := hside t (fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx)) hmt
      ht_nd ht_ch
    have hpos : 1 ≤ 2 ^ H := Nat.one_le_two_pow
    rw [List.length_append, List.length_cons, Nat.pow_succ]
    omega
end DeciSigma1.Arithmetic
