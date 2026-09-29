-- Prove2me | solution 1 for Chou.fg_of_isFinitelyPresented_quotient
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:42:27.243029+00:00
-- url     : https://prove2.me/submissions/f23284d3-85a8-4dde-aa5c-39c2f96f7a4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Chou_Growth
import Mathlib
import Theorems.Thm_Chou_fg_of_isFinitelyPresented_quotient_of_not_hasFreeSubsemigroupOfRankTwo

namespace Chou

lemma wordBall_mono {G : Type*} [Group G] {S : Set G} {m n : ℕ} (h : m ≤ n) :
    wordBall S m ⊆ wordBall S n := by
  rintro g ⟨l, hl, hS, rfl⟩
  exact ⟨l, hl.trans h, hS, rfl⟩

lemma wordBall_mul {G : Type*} [Group G] {S : Set G} {m n : ℕ} {g h : G}
    (hg : g ∈ wordBall S m) (hh : h ∈ wordBall S n) : g * h ∈ wordBall S (m + n) := by
  obtain ⟨l, hl, hS, rfl⟩ := hg
  obtain ⟨l', hl', hS', rfl⟩ := hh
  refine ⟨l ++ l', by simp; omega, fun x hx => ?_, by simp⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact hS x hx
  · exact hS' x hx

lemma wordBall_finite {G : Type*} [Group G] (S : Finset G) (n : ℕ) :
    (wordBall (S : Set G) n).Finite := by
  classical
  let T : Finset G := S ∪ S.image (fun x => x⁻¹)
  have hfin : {l : List T | l.length ≤ n}.Finite := List.finite_length_le T n
  refine (hfin.image (fun l : List T => (l.map Subtype.val).prod)).subset ?_
  rintro g ⟨l, hl, hS, rfl⟩
  have hmem : ∀ x ∈ l, x ∈ T := by
    intro x hx
    rcases hS x hx with h | h
    · exact Finset.mem_union_left _ (by exact_mod_cast h)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨x⁻¹, by exact_mod_cast h, inv_inv x⟩)
  refine ⟨l.attach.map (fun x => ⟨x.1, hmem x.1 x.2⟩), by simpa using hl, ?_⟩
  simp only [List.map_map]
  congr 1
  simp [Function.comp_def]

lemma not_free_of_expBounded {G : Type*} [Group G] (hb : IsExponentiallyBounded G) :
    ¬ HasFreeSubsemigroupOfRankTwo G := by
  rintro ⟨a, b, hinj⟩
  obtain ⟨S, hS, hbound⟩ := hb
  -- every element lies in some word ball
  have hball : ∀ g : G, ∃ L : ℕ, g ∈ wordBall (S : Set G) L := by
    intro g
    have : g ∈ Subgroup.closure (S : Set G) := by rw [hS]; trivial
    have h2 : g ∈ Submonoid.closure ((S : Set G) ∪ (S : Set G)⁻¹) := by
      rw [← Subgroup.closure_toSubmonoid]; exact this
    obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure h2
    refine ⟨l.length, l, le_rfl, fun x hx => ?_, hprod⟩
    rcases hl x hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  obtain ⟨La, ha⟩ := hball a
  obtain ⟨Lb, hb'⟩ := hball b
  set L := max (max La Lb) 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hab : ∀ i : Fin 2, ![a, b] i ∈ wordBall (S : Set G) L := by
    intro i
    fin_cases i
    · exact wordBall_mono (le_trans (le_max_left _ _) (le_max_left _ _)) ha
    · exact wordBall_mono (le_trans (le_max_right _ _) (le_max_left _ _)) hb'
  have hword : ∀ w : List (Fin 2),
      FreeMonoid.lift ![a, b] (FreeMonoid.ofList w) ∈ wordBall (S : Set G) (L * w.length) := by
    intro w
    induction w with
    | nil => exact ⟨[], by simp, by simp, by simp⟩
    | cons x w ih =>
      have := wordBall_mul (hab x) ih
      rw [show L * (x :: w).length = L + L * w.length by simp [List.length_cons]; ring]
      simpa [FreeMonoid.ofList_cons] using this
  -- cardinality lower bound
  have hcard : ∀ n : ℕ, (2 : ℝ) ^ n ≤ Nat.card (wordBall (S : Set G) (L * n)) := by
    intro n
    have hfin := (wordBall_finite S (L * n)).to_subtype
    let f : (Fin n → Fin 2) → wordBall (S : Set G) (L * n) := fun w =>
      ⟨FreeMonoid.lift ![a, b] (FreeMonoid.ofList (List.ofFn w)), by
        simpa using hword (List.ofFn w)⟩
    have hf : Function.Injective f := by
      intro w w' h
      have h1 := congrArg Subtype.val h
      have h2 := hinj h1
      exact List.ofFn_injective (FreeMonoid.ofList.injective h2)
    have := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] at this
    exact_mod_cast this
  -- choose c = 2^(1/(2L))
  have hc : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (2 * L)) := by
    apply Real.one_lt_rpow (by norm_num)
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  obtain ⟨N, hN⟩ := hbound _ hc
  set n := N + 1
  have h1 := hcard n
  have h2 := hN (L * n) (le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left _ (by omega)))
  have h3 : ((2 : ℝ) ^ ((1 : ℝ) / (2 * L))) ^ (L * n) = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    have : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    push_cast
    field_simp
  rw [h3] at h2
  have h4 : (2 : ℝ) ^ ((n : ℝ) / 2) < (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  linarith

theorem _root_.solution {G : Type*} [Group G] [Group.FG G] (hb : IsExponentiallyBounded G)
    (N : Subgroup G) [N.Normal] [Group.IsFinitelyPresented (G ⧸ N)] : Group.FG N :=
  fg_of_isFinitelyPresented_quotient_of_not_hasFreeSubsemigroupOfRankTwo
    (not_free_of_expBounded hb) N

end Chou
