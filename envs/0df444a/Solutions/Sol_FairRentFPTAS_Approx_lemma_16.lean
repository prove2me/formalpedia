-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:20:10.901467+00:00
-- url     : https://prove2.me/submissions/f28eb39c-7ac1-4957-aa01-3ef9b7e4070f

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FRFL16Aux

variable {n : ℕ}

/-- cost of a path (list of vertices) under edge costs `c`. -/
noncomputable def pc (c : Fin n → Fin n → ℝ) : List (Fin n) → ℝ
  | x :: y :: t => c x y + pc c (y :: t)
  | _ => 0

lemma pc_append_single (c : Fin n → Fin n → ℝ) (L : List (Fin n)) (hL : L ≠ []) (u : Fin n) :
    pc c (L ++ [u]) = pc c L + c (L.getLast hL) u := by
  induction L with
  | nil => exact absurd rfl hL
  | cons y t ih =>
    cases t with
    | nil => simp [pc]
    | cons z t' =>
      have := ih (List.cons_ne_nil _ _)
      simp only [List.cons_append, pc] at this ⊢
      rw [this, List.getLast_cons (List.cons_ne_nil _ _)]
      ring

lemma pc_split (c : Fin n → Fin n → ℝ) (A B : List (Fin n)) (x : Fin n) :
    pc c (A ++ x :: B) = pc c (A ++ [x]) + pc c (x :: B) := by
  induction A with
  | nil => simp [pc]
  | cons y t ih =>
    cases t with
    | nil => simp [pc]
    | cons z t' =>
      simp only [List.cons_append, pc] at ih ⊢
      rw [ih]; ring

/-- the cyclic sum along `formPerm` equals the cost of the closed path. -/
lemma cyc_sum (c : Fin n → Fin n → ℝ) (hc : ∀ x, c x x = 0) :
    ∀ (L : List (Fin n)) (hL : L ≠ []), L.Nodup →
      ∑ x, c x (L.formPerm x) = pc c (L ++ [L.head hL]) := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons y t ih =>
    intro _ hnd
    cases t with
    | nil => simp [pc, hc]
    | cons z t' =>
      have hnd' : (z :: t').Nodup := hnd.of_cons
      have hy : y ∉ z :: t' := (List.nodup_cons.mp hnd).1
      have IH := ih (List.cons_ne_nil _ _) hnd'
      set ρ0 := (z :: t').formPerm with hρ0
      set w := (z :: t').getLast (List.cons_ne_nil _ _) with hw
      have hρy : ρ0 y = y := List.formPerm_apply_of_notMem hy
      have hρw : ρ0 w = z := List.formPerm_apply_getLast z t'
      have hwmem : w ∈ z :: t' := List.getLast_mem _
      have hyw : y ≠ w := fun h => hy (h ▸ hwmem)
      have hyz : y ≠ z := fun h => hy (h ▸ List.mem_cons_self)
      rw [List.formPerm_cons_cons]
      have key : ∑ x, c x ((Equiv.swap y z * ρ0) x) - ∑ x, c x (ρ0 x) =
          (c y z - c y y) + (c w y - c w z) := by
        rw [← Finset.sum_sub_distrib]
        rw [Fintype.sum_eq_add y w hyw]
        · simp only [Equiv.Perm.mul_apply, hρy, hρw, Equiv.swap_apply_left,
            Equiv.swap_apply_right]
        · intro x ⟨hx1, hx2⟩
          simp only [Equiv.Perm.mul_apply]
          have h1 : ρ0 x ≠ y := by
            intro h; apply hx1; rw [← hρy] at h; exact ρ0.injective h
          have h2 : ρ0 x ≠ z := by
            intro h; apply hx2; rw [← hρw] at h; exact ρ0.injective h
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; ring
      have e1 : pc c ((y :: z :: t') ++ [y]) = c y z + pc c ((z :: t') ++ [y]) := by
        simp [pc]
      have e2 := pc_append_single c (z :: t') (List.cons_ne_nil _ _) y
      have e3 := pc_append_single c (z :: t') (List.cons_ne_nil _ _) z
      simp only [List.head_cons] at IH ⊢
      rw [e1, e2]
      rw [e3] at IH
      rw [hc] at key
      linarith

/-- Potential lemma: for a maximum-weight permutation `π`, there are prices supporting it. -/
theorem potentials (B : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (hmax : ∀ σ : Equiv.Perm (Fin n), ∑ a, B a (σ a) ≤ ∑ a, B a (π a)) :
    ∃ p : Fin n → ℝ, ∀ a r, B a r - p r ≤ B a (π a) - p (π a) := by
  classical
  let c : Fin n → Fin n → ℝ := fun x y => B (π.symm x) x - B (π.symm x) y
  have hc : ∀ x, c x x = 0 := fun x => by simp [c]
  -- nonnegativity of cycles
  have hcyc : ∀ (L : List (Fin n)) (hL : L ≠ []), L.Nodup → 0 ≤ pc c (L ++ [L.head hL]) := by
    intro L hL hnd
    rw [← cyc_sum c hc L hL hnd]
    set ρ := L.formPerm
    have h1 := hmax (π.trans ρ)
    have h2 : ∑ x, c x (ρ x) = ∑ a, B a (π a) - ∑ a, B a ((π.trans ρ) a) := by
      rw [← Finset.sum_sub_distrib]
      rw [← Equiv.sum_comp π (fun x => c x (ρ x))]
      apply Finset.sum_congr rfl
      intro a _
      simp [c]
    linarith
  -- the set of simple paths starting at x
  let S : Fin n → Set (List (Fin n)) := fun x => {l | l.Nodup ∧ l.head? = some x}
  have hfin : ∀ x, (S x).Finite := by
    intro x
    apply (List.finite_length_le (α := Fin n) n).subset
    intro l hl
    have := hl.1.length_le_card
    simpa using this
  have hne : ∀ x, (S x).Nonempty := fun x => ⟨[x], by simp [S]⟩
  have hmin : ∀ x, ∃ l ∈ S x, ∀ l' ∈ S x, pc c l ≤ pc c l' := fun x =>
    Set.exists_min_image (S x) (pc c) (hfin x) (hne x)
  choose m hmS hmle using hmin
  refine ⟨fun x => pc c (m x), ?_⟩
  -- key inequality
  have hkey : ∀ x r, pc c (m x) ≤ c x r + pc c (m r) := by
    intro x r
    by_cases hxr : x = r
    · subst hxr; rw [hc]; simp
    obtain ⟨hnd, hhd⟩ := hmS r
    obtain ⟨A', hA'⟩ : ∃ A', m r = r :: A' := by
      cases h : m r with
      | nil => rw [h] at hhd; simp at hhd
      | cons y t => rw [h] at hhd; simp at hhd; exact ⟨t, by rw [hhd]⟩
    by_cases hxm : x ∈ m r
    · obtain ⟨A, B', hsplit⟩ := List.append_of_mem hxm
      have hndAB : (A ++ x :: B').Nodup := hsplit ▸ hnd
      have hA : A ≠ [] := by
        intro hA; rw [hA] at hsplit; rw [hA'] at hsplit
        simp at hsplit; exact hxr hsplit.1.symm
      obtain ⟨A'', hA''⟩ : ∃ A'', A = r :: A'' := by
        cases A with
        | nil => exact absurd rfl hA
        | cons y t =>
          rw [hA'] at hsplit; simp at hsplit; exact ⟨t, by rw [hsplit.1]⟩
      -- path from x
      have hxB : x :: B' ∈ S x := by
        refine ⟨?_, by simp⟩
        exact (List.nodup_append.mp hndAB).2.1
      have hmx := hmle x (x :: B') hxB
      -- cycle
      have hndA : A.Nodup := (List.nodup_append.mp hndAB).1
      have hxA : x ∉ A := by
        intro h
        have := (List.nodup_append.mp hndAB).2.2 x h x List.mem_cons_self
        exact this rfl
      have hcy := hcyc (x :: A) (List.cons_ne_nil _ _) (List.nodup_cons.mpr ⟨hxA, hndA⟩)
      simp only [List.head_cons] at hcy
      have e1 : pc c (x :: A ++ [x]) = c x r + pc c (A ++ [x]) := by
        rw [hA'']; simp [pc]
      have e2 := pc_split c A B' x
      rw [← hsplit] at e2
      linarith
    · have hxS : x :: m r ∈ S x := ⟨List.nodup_cons.mpr ⟨hxm, hnd⟩, by simp⟩
      have := hmle x _ hxS
      have e : pc c (x :: m r) = c x r + pc c (m r) := by rw [hA']; simp [pc]
      linarith
  intro a r
  have := hkey (π a) r
  simp only [c, Equiv.symm_apply_apply] at this
  linarith

end FRFL16Aux

theorem solution {n : ℕ} (B : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    (∃ p : Fin n → ℝ, ∀ a r, B a r - p r ≤ B a (π a) - p (π a)) ↔
      ∀ σ : Equiv.Perm (Fin n), ∑ a, B a (σ a) ≤ ∑ a, B a (π a) := by
  constructor
  · rintro ⟨p, hp⟩ σ
    have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hp a (σ a))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h
    have e1 : ∑ a, p (σ a) = ∑ r, p r := Equiv.sum_comp σ p
    have e2 : ∑ a, p (π a) = ∑ r, p r := Equiv.sum_comp π p
    linarith
  · exact FRFL16Aux.potentials B π
