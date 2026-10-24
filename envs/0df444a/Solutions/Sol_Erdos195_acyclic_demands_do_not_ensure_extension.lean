-- Prove2me | solution 1 for Erdos195.acyclic_demands_do_not_ensure_extension
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:37:13.298213+00:00
-- url     : https://prove2.me/submissions/36ec39d3-91b8-4ba1-b293-896a8735e357

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195.ExtensionDependencies

/-- The finite in-order triple condition from the accepted tree-order development. -/
def APClosed (P : List ℤ) : Prop :=
  ∀ a b : ℤ, a ∈ P → b ∈ P → 2 * b - a ∈ P → P.idxOf a < P.idxOf b →
    P.idxOf b < P.idxOf (2 * b - a) →
    3 * b - 2 * a ∈ P ∧ P.idxOf (3 * b - 2 * a) < P.idxOf (2 * b - a)

/-- Safety forces the fourth term of an in-order triple to occur before its third term. -/
lemma safe_apClosed {R : ℤ → ℤ → Prop} {P : List ℤ} (hS : Safe R P) :
    APClosed P := by
  intro a b ha hb hc hab hbc
  have hr : b - a ≠ 0 := by
    intro h
    have : b = a := sub_eq_zero.mp h
    subst b
    exact lt_irrefl _ hab
  have hfirst : compLt R P a b := Or.inl ⟨ha, hb, hab⟩
  have hsecond : compLt R P b (2 * b - a) := Or.inl ⟨hb, hc, hbc⟩
  have e1 : a + (b - a) = b := by ring
  have e2 : a + 2 * (b - a) = 2 * b - a := by ring
  have e3 : a + 3 * (b - a) = 3 * b - 2 * a := by ring
  have hlast : ¬ compLt R P (2 * b - a) (3 * b - 2 * a) := by
    intro h
    apply hS a (b - a) hr
    rw [e1, e2, e3]
    exact ⟨hfirst, hsecond, h⟩
  have hd : 3 * b - 2 * a ∈ P := by
    by_contra h
    exact hlast (Or.inr (Or.inl ⟨hc, h⟩))
  have hnot : ¬ P.idxOf (2 * b - a) < P.idxOf (3 * b - 2 * a) :=
    fun h => hlast (Or.inl ⟨hc, hd, h⟩)
  have hne : P.idxOf (3 * b - 2 * a) ≠ P.idxOf (2 * b - a) := by
    intro h
    have hval := (List.idxOf_inj hd).1 h
    apply hr
    omega
  exact ⟨hd, by omega⟩

lemma safe_false_iff (P : List ℤ) : Safe (fun _ _ => False) P ↔ APClosed P := by
  refine ⟨safe_apClosed, ?_⟩
  intro hP a r _hr ⟨h1, h2, h3⟩
  have left_mem : ∀ x y, compLt (fun _ _ => False) P x y → x ∈ P := by
    intro x y h
    rcases h with h | h | h
    · exact h.1
    · exact h.1
    · exact h.2.2.elim
  have pair : ∀ x y, y ∈ P → compLt (fun _ _ => False) P x y →
      x ∈ P ∧ P.idxOf x < P.idxOf y := by
    intro x y hy h
    rcases h with h | h | h
    · exact ⟨h.1, h.2.2⟩
    · exact (h.2 hy).elim
    · exact h.2.2.elim
  have hc := left_mem _ _ h3
  obtain ⟨hb, hbc⟩ := pair _ _ hc h2
  obtain ⟨ha, hab⟩ := pair _ _ hb h1
  have e2 : 2 * (a + r) - a = a + 2 * r := by ring
  have e3 : 3 * (a + r) - 2 * a = a + 3 * r := by ring
  have hcont := hP a (a + r) ha hb (by rwa [e2]) hab (by rwa [e2])
  rw [e2, e3] at hcont
  have hcd := (pair _ _ hcont.1 h3).2
  have hdc := hcont.2
  omega

/-- An old ordered pair forces the missing fourth term `d` before the missing third term `c`. -/
def Needs (P : List ℤ) (c d : ℤ) : Prop :=
  c ∉ P ∧ d ∉ P ∧ ∃ a ∈ P, ∃ b ∈ P,
    P.idxOf a < P.idxOf b ∧ c = 2 * b - a ∧ d = 3 * b - 2 * a

/-- Every demand becomes a strict decrease of positions in any safe prefix extension. -/
lemma needs_position {P Q : List ℤ} {R : ℤ → ℤ → Prop}
    (hpre : P <+: Q) (hS : Safe R Q) {c d : ℤ} (h : Needs P c d) (hc : c ∈ Q) :
    d ∈ Q ∧ Q.idxOf d < Q.idxOf c := by
  obtain ⟨hcn, _hdn, a, ha, b, hb, hab, rfl, rfl⟩ := h
  obtain ⟨S, rfl⟩ := hpre
  apply safe_apClosed hS a b (List.mem_append_left _ ha) (List.mem_append_left _ hb) hc
  · simpa only [List.idxOf_append, if_pos ha, if_pos hb] using hab
  · rw [List.idxOf_append, if_pos hb, List.idxOf_append, if_neg hcn]
    have := List.idxOf_lt_length_of_mem hb
    omega

lemma needs_path_position {P Q : List ℤ} {R : ℤ → ℤ → Prop}
    (hpre : P <+: Q) (hS : Safe R Q) {c d : ℤ}
    (h : Relation.TransGen (Needs P) c d) (hc : c ∈ Q) :
    d ∈ Q ∧ Q.idxOf d < Q.idxOf c := by
  induction h with
  | single h => exact needs_position hpre hS h hc
  | tail _ h ih =>
    obtain ⟨he, hec⟩ := ih
    obtain ⟨hd, hde⟩ := needs_position hpre hS h he
    exact ⟨hd, hde.trans hec⟩

/-- A directed cycle of missing-continuation demands can never be entered by a safe extension. -/
theorem cycle_blocks_extension {P Q : List ℤ} {R : ℤ → ℤ → Prop}
    (hpre : P <+: Q) (hS : Safe R Q) {c : ℤ}
    (hcycle : Relation.TransGen (Needs P) c c) : c ∉ Q := by
  intro hc
  exact lt_irrefl _ (needs_path_position hpre hS hcycle hc).2

/-- The weaker stage invariant admits this one-helper escape from the tree-search prefix. -/
theorem pstar_escape : Safe (fun _ _ => False) [0, 1, -1, -5, 3, 2] := by
  rw [safe_false_iff]
  intro a b ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [List.idxOf_cons]

lemma pstar_needs_outward {c d : ℤ} (h : Needs [0, 1, -1, -5, 3, 2] c d) :
    |c| < |d| := by
  obtain ⟨hcn, hdn, a, ha, b, hb, hab, rfl, rfl⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [List.idxOf_cons] at *

/-- The non-tree escape also avoids the finite dependency-cycle obstruction. -/
theorem pstar_needs_acyclic (c : ℤ) :
    ¬ Relation.TransGen (Needs [0, 1, -1, -5, 3, 2]) c c := by
  intro h
  have hpath : ∀ {a b : ℤ},
      Relation.TransGen (Needs [0, 1, -1, -5, 3, 2]) a b → |a| < |b| := by
    intro a b h
    induction h with
    | single h => exact pstar_needs_outward h
    | tail _ h ih => exact ih.trans (pstar_needs_outward h)
  exact lt_irrefl _ (hpath h)

/-- This prefix is safe for the empty tail relation, despite having an unavoidable deadlock. -/
theorem deadlock_safe : Safe (fun _ _ => False) [-2, -1, 3, 2] := by
  rw [safe_false_iff]
  intro a b ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    norm_num [List.idxOf_cons]

lemma deadlock_zero_one : Needs [-2, -1, 3, 2] 0 1 := by
  refine ⟨by norm_num, by norm_num, -2, by norm_num, -1, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [List.idxOf_cons]

lemma deadlock_one_zero : Needs [-2, -1, 3, 2] 1 0 := by
  refine ⟨by norm_num, by norm_num, 3, by norm_num, 2, by norm_num, ?_, ?_, ?_⟩ <;>
    norm_num [List.idxOf_cons]

/-- No choice or change of tail relation can repair this prefix to include either missing value. -/
theorem deadlock_no_extension (R : ℤ → ℤ → Prop) (Q : List ℤ)
    (hpre : [-2, -1, 3, 2] <+: Q) (hS : Safe R Q) : (0 : ℤ) ∉ Q ∧ (1 : ℤ) ∉ Q := by
  constructor
  · exact cycle_blocks_extension hpre hS
      ((Relation.TransGen.single deadlock_zero_one).tail deadlock_one_zero)
  · exact cycle_blocks_extension hpre hS
      ((Relation.TransGen.single deadlock_one_zero).tail deadlock_zero_one)

end Erdos195.ExtensionDependencies

namespace Erdos195.ExtensionDependencies

/-- A second-order deadlock whose initial demand graph has no directed cycle. -/
def secondTrap : List ℤ := [0, 3, 2, 11, 10]

/-- Swap 8 and 9 in the numerical ranking to orient every initial demand. -/
def secondTrapRank (x : ℤ) : ℤ := if x = 9 then 8 else if x = 8 then 9 else x

theorem secondTrap_safe : Safe (fun _ _ => False) secondTrap := by
  rw [safe_false_iff]
  intro a b ha hb
  simp only [secondTrap, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [secondTrap, List.idxOf_cons]

lemma secondTrap_needs_increases {c d : ℤ} (h : Needs secondTrap c d) :
    secondTrapRank c < secondTrapRank d := by
  obtain ⟨hcn, hdn, a, ha, b, hb, hab, rfl, rfl⟩ := h
  simp only [secondTrap, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [secondTrap, secondTrapRank, List.idxOf_cons] at *

theorem secondTrap_needs_acyclic (c : ℤ) : ¬ Relation.TransGen (Needs secondTrap) c c := by
  intro h
  have hpath : ∀ {a b : ℤ}, Relation.TransGen (Needs secondTrap) a b →
      secondTrapRank a < secondTrapRank b := by
    intro a b h
    induction h with
    | single h => exact secondTrap_needs_increases h
    | tail _ h ih => exact ih.trans (secondTrap_needs_increases h)
  exact lt_irrefl _ (hpath h)

lemma secondTrap_four_six : Needs secondTrap 4 6 := by
  refine ⟨by norm_num [secondTrap], by norm_num [secondTrap],
    0, by norm_num [secondTrap], 2, by norm_num [secondTrap], ?_, ?_, ?_⟩ <;>
    norm_num [secondTrap, List.idxOf_cons]

lemma secondTrap_six_nine : Needs secondTrap 6 9 := by
  refine ⟨by norm_num [secondTrap], by norm_num [secondTrap],
    0, by norm_num [secondTrap], 3, by norm_num [secondTrap], ?_, ?_, ?_⟩ <;>
    norm_num [secondTrap, List.idxOf_cons]

lemma secondTrap_nine_eight : Needs secondTrap 9 8 := by
  refine ⟨by norm_num [secondTrap], by norm_num [secondTrap],
    11, by norm_num [secondTrap], 10, by norm_num [secondTrap], ?_, ?_, ?_⟩ <;>
    norm_num [secondTrap, List.idxOf_cons]

/-- Acyclicity of the initial demands is not sufficient for prescribed-target extension. -/
theorem secondTrap_no_four (R : ℤ → ℤ → Prop) (Q : List ℤ)
    (hpre : secondTrap <+: Q) (hS : Safe R Q) : (4 : ℤ) ∉ Q := by
  intro h4
  obtain ⟨h6, hi64⟩ := needs_position hpre hS secondTrap_four_six h4
  obtain ⟨h9, hi96⟩ := needs_position hpre hS secondTrap_six_nine h6
  obtain ⟨h8, hi89⟩ := needs_position hpre hS secondTrap_nine_eight h9
  have h10 : (10 : ℤ) ∈ Q := hpre.subset (by simp [secondTrap])
  have hi108 : Q.idxOf (10 : ℤ) < Q.idxOf (8 : ℤ) := by
    obtain ⟨S, rfl⟩ := hpre
    norm_num [secondTrap, List.idxOf_append, List.idxOf_cons]
  have h := safe_apClosed hS 10 8 h10 h8
    (by norm_num; exact h6) hi108 (by norm_num; exact hi89.trans hi96)
  norm_num at h
  exact lt_asymm hi64 h.2

/-- In particular, even arbitrary stage-dependent tail relations cannot exhaust from this prefix. -/
theorem secondTrap_no_exhaustion (R : ℕ → ℤ → ℤ → Prop) (P : ℕ → List ℤ)
    (hpre : ∀ n, secondTrap <+: P n) (hsafe : ∀ n, Safe (R n) (P n))
    (hcov : ∀ x : ℤ, ∃ n, x ∈ P n) : False := by
  obtain ⟨n, hn⟩ := hcov 4
  exact secondTrap_no_four (R n) (P n) (hpre n) (hsafe n) hn

end Erdos195.ExtensionDependencies

/-- Initial continuation-demand acyclicity does not ensure prescribed-target extension. -/
theorem solution :
    let P : List ℤ := [0, 3, 2, 11, 10]
    let D : ℤ → ℤ → Prop := fun c d =>
      c ∉ P ∧ d ∉ P ∧ ∃ a ∈ P, ∃ b ∈ P,
        P.idxOf a < P.idxOf b ∧ c = 2 * b - a ∧ d = 3 * b - 2 * a
    Erdos195.Safe (fun _ _ => False) P ∧
      (∀ c : ℤ, ¬ Relation.TransGen D c c) ∧
      ∀ (R : ℤ → ℤ → Prop) (Q : List ℤ),
        P <+: Q → Erdos195.Safe R Q → (4 : ℤ) ∉ Q := by
  exact ⟨Erdos195.ExtensionDependencies.secondTrap_safe,
    Erdos195.ExtensionDependencies.secondTrap_needs_acyclic,
    Erdos195.ExtensionDependencies.secondTrap_no_four⟩
