-- Prove2me | solution 1 for ConantTerry.Orders.theorem_1_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:48.511414+00:00
-- url     : https://prove2.me/submissions/d292cb30-429a-48ef-813f-d198cb0bc5e6

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_ladder
import Definitions.Def_ConantTerry_Orders_extraction_height
import Theorems.Thm_ConantTerry_Orders_extraction_recurrence
import Theorems.Thm_ConantTerry_Orders_restrict_tree

section
set_option autoImplicit false
namespace ConantTerry.Dev.Thm11
open ConantTerry.Orders

theorem unwrap {X : Type*} {Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (k ℓ : ℕ)
    (n : ℕ) (h : extractionHeight f δ k ℓ = (n : WithTop ℕ)) :
    1 ≤ n ∧ ExtractionP f δ k ℓ n := by
  classical
  unfold extractionHeight at h
  by_cases hex : ∃ t : ℕ, 1 ≤ t ∧ ExtractionP f δ k ℓ t
  · rw [dif_pos hex] at h
    have : Nat.find hex = n := by exact_mod_cast h
    rw [← this]; exact Nat.find_spec hex
  · rw [dif_neg hex] at h; exact absurd h (by simp)

theorem bound {X : Type*} {Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ n a b : ℕ, a + b = n → ∃ T : ℕ, extractionHeight f δ (a+1) (b+1) = (T : WithTop ℕ) ∧
      T + 1 ≤ 2 * Nat.choose (a + b) a := by
  have hrec := extraction_recurrence f δ hδ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have := (hrec.1 1 (b+1) le_rfl (by omega)).2
      refine ⟨1, by simpa using this, ?_⟩
      simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have := (hrec.1 (a+1) 1 (by omega) le_rfl).1
      refine ⟨1, by simpa using this, ?_⟩
      simp
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨T1, h1, hb1⟩ := ih (n - 1) (by omega) a' (b'+1) (by omega)
    obtain ⟨T2, h2, hb2⟩ := ih (n - 1) (by omega) (a'+1) b' (by omega)
    have h1' : extractionHeight f δ (a'+1+1-1) (b'+1+1) ≠ ⊤ := by
      have : a'+1+1-1 = a'+1 := rfl
      rw [this, h1]; simp
    have h2' : extractionHeight f δ (a'+1+1) (b'+1+1-1) ≠ ⊤ := by
      have : b'+1+1-1 = b'+1 := rfl
      rw [this, h2]; simp
    obtain ⟨hne, hle⟩ := (hrec.2 (a'+1+1) (b'+1+1) (by omega) (by omega) h1' h2')
    have e1 : a'+1+1-1 = a'+1 := rfl
    have e2 : b'+1+1-1 = b'+1 := rfl
    rw [e1, h1] at hle
    rw [e2, h2] at hle
    obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.mp hne
    refine ⟨T, hT.symm, ?_⟩
    rw [← hT] at hle
    have hle' : T ≤ T1 + T2 + 1 := WithTop.coe_le_coe.mp (by push_cast; exact hle)
    have hc : Nat.choose (a'+1+(b'+1)) (a'+1) = Nat.choose (a'+(b'+1)) a' + Nat.choose (a'+1+b') (a'+1) := by
      have := Nat.choose_succ_succ (a' + b' + 1) a'
      have e : a'+1+(b'+1) = a'+b'+1+1 := by omega
      have e' : a'+(b'+1) = a'+b'+1 := by omega
      have e'' : a'+1+b' = a'+b'+1 := by omega
      rw [e, e', e'']; exact this
    omega

theorem inclusion_embedding (T t : ℕ) (hTt : T ≤ t) :
    ∃ φ : WordsAtMost T → WordsAtMost t, IsProperEmbedding φ := by
  have hlen : ∀ σ : WordsAtMost T, (if σ.val.length = T then σ.val ++ List.replicate (t - T) false
      else σ.val).length ≤ t := by
    intro σ
    have h0 : σ.val.length ≤ T := σ.property
    split_ifs with h <;> simp <;> omega
  refine ⟨fun σ => ⟨if σ.val.length = T then σ.val ++ List.replicate (t - T) false else σ.val, hlen σ⟩, ?_, ?_⟩
  · intro σ τ a h
    have hl := h.length_le
    simp only [List.length_append, List.length_singleton] at hl
    have hτ0 : τ.val.length ≤ T := τ.property
    have hσ : σ.val.length ≠ T := by omega
    dsimp only
    rw [if_neg hσ]
    split_ifs with hτ
    · exact h.trans (List.prefix_append _ _)
    · exact h
  · intro σ hσ
    dsimp only
    rw [if_pos hσ]; simp; omega

end ConantTerry.Dev.Thm11

namespace ConantTerry.Orders
open ConantTerry.Dev.Thm11 in
theorem chk_theorem_1_11 {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k)
    (δ : ℝ) (hδ : 0 < δ)
    (hTree : AdmitsTree f (Nat.choose (2 * k) k - 1) (2 * δ)) :
    AdmitsLadder f k δ := by
  obtain ⟨x, y, r, hT⟩ := hTree
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  obtain ⟨T, hTeq, hTb⟩ := bound f δ hδ _ a (a + 1) rfl
  obtain ⟨hT1, hP⟩ := unwrap f δ (a + 1) (a + 1 + 1) T hTeq
  have hc : Nat.choose (2 * (a + 1)) (a + 1) = 2 * Nat.choose (a + (a + 1)) a := by
    have h1 := Nat.choose_succ_succ (a + (a + 1)) a
    have h2 := Nat.choose_symm_add (a := a) (b := a + 1)
    have e : 2 * (a + 1) = (a + (a + 1)).succ := by omega
    rw [e]
    simp only [Nat.succ_eq_add_one] at h1 ⊢
    omega
  have hTt : T ≤ Nat.choose (2 * (a + 1)) (a + 1) - 1 := by omega
  obtain ⟨φ, hφ⟩ := inclusion_embedding T _ hTt
  obtain ⟨nodes, leaves, -, -, hT'⟩ :=
    restrict_tree f T _ hT1 (by omega) (2 * δ) (by positivity) x y r hT φ hφ
  rcases hP _ _ _ hT' with ⟨α, β, h⟩ | ⟨α, β, h⟩
  · refine ⟨fun i => x (nodes (α (Fin.rev i))), fun i => y (leaves (β (Fin.rev i))),
      fun i => r (nodes (α (Fin.rev i))), ?_⟩
    intro i j
    constructor
    · intro hij
      exact (h (Fin.rev j) (Fin.rev i)).1 (Fin.rev_le_rev.mpr hij)
    · intro hji
      exact (h (Fin.rev i) (Fin.rev j)).2 (Fin.rev_lt_rev.mpr hji)
  · have hle : ∀ i : Fin (a + 1), (r (nodes (α i.castSucc)) : ℝ) + δ ≤ 1 := by
      intro i
      have h1 := (h i.castSucc i.succ).2 (by simp [Fin.lt_def])
      have h2 := (f (x (nodes (α i.castSucc)), y (leaves (β i.succ)))).2.2
      simp only [Function.comp] at h1
      linarith
    refine ⟨fun i => x (nodes (α i.castSucc)), fun i => y (leaves (β i.succ)),
      fun i => ⟨(r (nodes (α i.castSucc)) : ℝ) + δ,
        add_nonneg (r (nodes (α i.castSucc))).2.1 hδ.le, hle i⟩, ?_⟩
    intro i j
    constructor
    · intro hij
      have := (h i.castSucc j.succ).2 (by simp [Fin.lt_def]; omega)
      simp only [Function.comp] at this ⊢
      linarith
    · intro hji
      have := (h j.succ i.castSucc).1 (by simp [Fin.le_def]; omega)
      simp only [Function.comp] at this ⊢
      linarith

end ConantTerry.Orders
end

theorem solution : type_of% @ConantTerry.Orders.chk_theorem_1_11 := @ConantTerry.Orders.chk_theorem_1_11
