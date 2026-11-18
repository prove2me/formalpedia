-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.corollary_15
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:12:51.555682+00:00
-- url     : https://prove2.me/submissions/f3dae714-cae4-44a2-9438-e10eff738db4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_14

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false

private lemma height_pos {n : ℕ} (hn : 2 ≤ n) : 0 < height n := by
  unfold height
  generalize he : (List.range (2 * n + 1)).find? (fun j => decide (2 ^ j * n ≤ 3 ^ j)) = o
  cases o with
  | none => simp; omega
  | some j =>
    simp only [Option.getD_some]
    have hj := List.find?_some he
    simp only [decide_eq_true_eq] at hj
    by_contra h
    have : j = 0 := by omega
    subst j
    norm_num at hj
    omega

private lemma accuracy_factor (B a n : ℕ) (ε : ℚ) (he : 0 < ε) (he1 : ε < 1) :
    1 - (ε : ℝ) ≤ (1 - ((parameters B a n ε).delta : ℝ)) ^ height n := by
  by_cases hn : n ≤ 1
  · simp [parameters, hn]
    exact_mod_cast le_of_lt he
  · have hh := height_pos (n := n) (by omega)
    have hhr : (0 : ℝ) < height n := by exact_mod_cast hh
    have heR : (0 : ℝ) < ε := by exact_mod_cast he
    have he1R : (ε : ℝ) < 1 := by exact_mod_cast he1
    have hdiv : (ε : ℝ) / height n ≤ 1 := by
      apply (div_le_iff₀ hhr).mpr
      have : (1 : ℝ) ≤ height n := by exact_mod_cast hh
      linarith
    have hb := one_add_mul_le_pow (a := -((ε : ℝ) / height n)) (by linarith : (-2 : ℝ) ≤ -((ε : ℝ) / height n)) (height n)
    have heq : (height n : ℝ) * -((ε : ℝ) / height n) = -(ε : ℝ) := by field_simp
    rw [heq] at hb
    simpa [parameters, hn, Rat.cast_div, Rat.cast_natCast, sub_eq_add_neg] using hb

theorem solution (C : GraphClass) (a : ℕ) (K : ℝ)
    (separatorClass : StronglyEdgeSublinear C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    ∃ (B : ℕ) (M : Routines), 0 < B ∧ PrimitiveContract C a B M ∧ SolveInvariant C a B M ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℚ),
        C n G → 0 < ε → ε < 1 →
        ∃ (I : Finset (Fin n)) (u : ℕ),
          Execute G (parameters B a n ε) M (.solve Finset.univ) (.solved I u) ∧
          G.IsIndepSet (I : Set (Fin n)) ∧
          (1 - (ε : ℝ)) * alpha G Finset.univ ≤ (I.card : ℝ) := by
  obtain ⟨B, M, hB, hprim, hinv⟩ := lemma_14 C a K separatorClass ha bound
  refine ⟨B, M, hB, hprim, hinv, ?_⟩
  intro n G ε hG he he1
  obtain ⟨I, u, hex⟩ := (hinv n G ε Finset.univ hG he he1).1
  obtain ⟨hsub, hind, halpha, hu, hsize⟩ := (hinv n G ε Finset.univ hG he he1).2 I u hex
  refine ⟨I, u, hex, hind, ?_⟩
  have hnon : (0 : ℝ) ≤ 1 - (ε : ℝ) := by exact_mod_cast (sub_nonneg.mpr he1.le)
  calc
    (1 - (ε : ℝ)) * alpha G Finset.univ ≤ (1 - (ε : ℝ)) * u :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast halpha) hnon
    _ ≤ (1 - ((parameters B a n ε).delta : ℝ)) ^ height n * u :=
      mul_le_mul_of_nonneg_right (accuracy_factor B a n ε he he1) (Nat.cast_nonneg _)
    _ ≤ I.card := by simpa using hsize
