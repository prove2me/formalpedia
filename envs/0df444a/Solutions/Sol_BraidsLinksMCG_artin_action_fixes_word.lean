-- Prove2me | solution 1 for BraidsLinksMCG.artin_action_fixes_word
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-14T12:23:00.728037+00:00
-- url     : https://prove2.me/submissions/c8f49072-a397-442f-aac6-3203a9f8c984

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

open BraidsLinksMCG

private lemma prod_ofFn_eq_range {G : Type} [Monoid G] (H : ℕ → G) (n : ℕ) :
    (List.ofFn fun j : Fin n => H (j : ℕ)).prod = ((List.range n).map H).prod := by
  induction n with
  | zero => simp
  | succ m ih => rw [List.ofFn_succ', List.range_succ]; simp [ih]

private lemma prod_range_swap {G : Type} [Group G] (g h : ℕ → G) (p : ℕ)
    (hlt : ∀ j, j < p → g j = h j) (hgt : ∀ j, p + 1 < j → g j = h j)
    (hpair : g p * g (p + 1) = h p * h (p + 1)) :
    ∀ N, p + 1 < N → ((List.range N).map g).prod = ((List.range N).map h).prod := by
  intro N
  induction N with
  | zero => omega
  | succ M ih =>
    intro hN
    rcases Nat.lt_or_ge (p + 1) M with hM | hM
    · rw [List.range_succ]
      simp [ih hM, hgt M (by omega)]
    · have hMe : M = p + 1 := by omega
      subst hMe
      have hpre : (List.range p).map g = (List.range p).map h :=
        List.map_congr_left fun j hj => hlt j (List.mem_range.mp hj)
      rw [List.range_succ, List.range_succ]
      simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, hpre]
      rw [mul_assoc, mul_assoc, hpair]

private lemma artinEndo_fixes (n : ℕ) (i : Fin (n - 1)) :
    artinEndo n i (freeWordProd n) = freeWordProd n := by
  have hi := i.isLt
  have hval : ∀ k : Fin n, artinEndo n i (FreeGroup.of k) =
      if k = strandIdx i then
        FreeGroup.of (strandIdx i) * FreeGroup.of (strandIdxSucc i) *
          (FreeGroup.of (strandIdx i))⁻¹
      else if k = strandIdxSucc i then FreeGroup.of (strandIdx i) else FreeGroup.of k := by
    intro k
    simp only [artinEndo, FreeGroup.lift_apply_of]
  set H : ℕ → FreeGroup (Fin n) :=
    fun k => if hk : k < n then FreeGroup.of (⟨k, hk⟩ : Fin n) else 1 with hH
  set g : ℕ → FreeGroup (Fin n) := fun k => artinEndo n i (H k) with hg
  have hW : freeWordProd n = ((List.range n).map H).prod := by
    rw [freeWordProd, show (fun j : Fin n => FreeGroup.of j) = (fun j : Fin n => H (j : ℕ)) from
      funext fun j => by simp [hH, j.isLt]]
    exact prod_ofFn_eq_range H n
  have hL : artinEndo n i (freeWordProd n) = ((List.range n).map g).prod := by
    rw [hW, map_list_prod, List.map_map]
    rfl
  rw [hL, hW]
  refine prod_range_swap g H (i : ℕ) ?_ ?_ ?_ n (by omega)
  · intro j hj
    have hjn : j < n := by omega
    simp only [hg, hH, dif_pos hjn, hval]
    rw [if_neg (by simp [strandIdx, Fin.ext_iff]; omega),
      if_neg (by simp [strandIdxSucc, Fin.ext_iff]; omega)]
  · intro j hj
    by_cases hjn : j < n
    · simp only [hg, hH, dif_pos hjn, hval]
      rw [if_neg (by simp [strandIdx, Fin.ext_iff]; omega),
        if_neg (by simp [strandIdxSucc, Fin.ext_iff]; omega)]
    · simp only [hg, hH, dif_neg hjn, map_one]
  · have h1 : (i : ℕ) < n := by omega
    have h2 : (i : ℕ) + 1 < n := by omega
    simp only [hg, hH, dif_pos h1, dif_pos h2, hval]
    rw [if_pos (by simp [strandIdx]), if_neg (by simp [strandIdx, Fin.ext_iff]),
      if_pos (by simp [strandIdxSucc])]
    simp [strandIdx, strandIdxSucc, mul_assoc]

open BraidsLinksMCG in
theorem solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (b : ArtinBraidGroup n) : xi b (freeWordProd n) = freeWordProd n := by
  have happ : ∀ (c d : ArtinBraidGroup n) (x : FreeGroup (Fin n)),
      xi (c * d) x = xi c (xi d x) := by
    intro c d x
    rw [map_mul, MulAut.mul_apply]
  have hinv : ∀ (c : ArtinBraidGroup n) (x : FreeGroup (Fin n)), xi c⁻¹ (xi c x) = x := by
    intro c x
    rw [← happ, inv_mul_cancel, map_one]
    rfl
  let S : Subgroup (ArtinBraidGroup n) :=
    { carrier := {c | xi c (freeWordProd n) = freeWordProd n}
      one_mem' := by
        show xi 1 (freeWordProd n) = freeWordProd n
        rw [map_one]
        rfl
      mul_mem' := by
        intro c d hc hd
        show xi (c * d) (freeWordProd n) = freeWordProd n
        rw [happ, hd, hc]
      inv_mem' := by
        intro c hc
        show xi c⁻¹ (freeWordProd n) = freeWordProd n
        conv_lhs => rw [← hc]
        exact hinv c (freeWordProd n) }
  have hgen : ∀ i : Fin (n - 1), sigma i ∈ S := by
    intro i
    show xi (sigma i) (freeWordProd n) = freeWordProd n
    rw [hxi i]
    exact artinEndo_fixes n i
  have hclos : Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i)) = ⊤ := by
    unfold sigma
    exact PresentedGroup.closure_range_of _
  have hle : Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i)) ≤ S :=
    (Subgroup.closure_le S).mpr (by rintro x ⟨i, rfl⟩; exact hgen i)
  exact hle (by rw [hclos]; trivial)
