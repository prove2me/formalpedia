-- Prove2me | solution 1 for DetComplexityPowerSum.Quadratic.claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:30:50.283169+00:00
-- url     : https://prove2.me/submissions/7dfb35b0-9329-479a-94f9-ba1815cb0a9f

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_PolarSlice
open MvPolynomial
open DetComplexityPowerSum.Quadratic

theorem dc_eval (n : ℕ) (a : Fin n → ℂ) : eval a (powerSum n) = ∑ i, a i ^ n := by
  simp [powerSum]

theorem dc_pderiv (n : ℕ) (a : Fin n → ℂ) (i : Fin n) :
    eval a (pderiv i (powerSum n)) = (n : ℂ) * a i ^ (n - 1) := by
  simp [powerSum, Derivation.leibniz_pow, pderiv_X, Pi.single_apply]

theorem dc_mem_iff (m : ℕ) (a : Fin (m + 2) → ℂ) :
    a ∈ polarSlice (m + 2) ↔
      (a (Fin.castSucc (Fin.last m)) = 1 ∧
        (∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 1) = 1) ∧
        a (Fin.last (m + 1)) ^ (m + 2) = -(1 + ∑ i : Fin m, a (Fin.castSucc (Fin.castSucc i)))) := by
  have hm : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have hsub : m + 2 - 1 = m + 1 := by omega
  have hpenj : ∀ j : Fin (m + 2), IsPenultimate j → j = Fin.castSucc (Fin.last m) := by
    intro j hj
    simp only [IsPenultimate] at hj
    ext
    simp only [Fin.val_castSucc, Fin.val_last]
    omega
  have hpen0 : IsPenultimate (Fin.castSucc (Fin.last m)) := by
    simp only [IsPenultimate, Fin.val_castSucc, Fin.val_last]
  have hsplit : ∑ i : Fin (m + 2), a i ^ (m + 2) =
      ∑ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 2) +
        a (Fin.castSucc (Fin.last m)) ^ (m + 2) + a (Fin.last (m + 1)) ^ (m + 2) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  unfold polarSlice
  simp only [Set.mem_ofPred_eq, dc_eval, dc_pderiv, hsub, hsplit]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hpen : a (Fin.castSucc (Fin.last m)) = 1 := h2 _ hpen0
    have hearly : ∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 1) = 1 := by
      intro i
      have := h3 (Fin.castSucc (Fin.castSucc i)) _
        (by simp only [IsEarly, Fin.val_castSucc]; omega) hpen0
      rw [hpen, one_pow] at this
      exact mul_left_cancel₀ hm this
    refine ⟨hpen, hearly, ?_⟩
    have hx : ∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 2) =
        a (Fin.castSucc (Fin.castSucc i)) := by
      intro i; rw [pow_succ, hearly i, one_mul]
    simp only [hx, hpen, one_pow] at h1
    linear_combination h1
  · rintro ⟨hpen, hearly, hlast⟩
    refine ⟨?_, ?_, ?_⟩
    · have hx : ∀ i : Fin m, a (Fin.castSucc (Fin.castSucc i)) ^ (m + 2) =
          a (Fin.castSucc (Fin.castSucc i)) := by
        intro i; rw [pow_succ, hearly i, one_mul]
      simp only [hx, hpen, one_pow, hlast]
      ring
    · intro j hj
      rw [hpenj j hj]
      exact hpen
    · intro i j hi hj
      rw [hpenj j hj, hpen, one_pow]
      have hi' : i.val < m := by simp only [IsEarly] at hi; omega
      have : i = Fin.castSucc (Fin.castSucc ⟨i.val, hi'⟩) := by ext; simp
      rw [this, hearly]

theorem solution {n : ℕ} (hn : 2 ≤ n) :
    (polarSlice n).Finite ∧ (n - 1) ^ (n - 2) ≤ (polarSlice n).ncard := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  set R : Finset ℂ := (Polynomial.nthRoots (m + 1) (1 : ℂ)).toFinset with hR
  have hRmem : ∀ z, z ∈ R ↔ z ^ (m + 1) = 1 := by
    intro z
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
  have hRcard : R.card = m + 1 := by
    have prim := Complex.isPrimitiveRoot_exp (m + 1) (by omega)
    rw [hR, Multiset.toFinset_card_of_nodup (IsPrimitiveRoot.nthRoots_one_nodup prim),
      IsPrimitiveRoot.card_nthRoots_one prim]
  have hfin : (polarSlice (m + 2)).Finite := by
    let W : Finset ℂ := (Finset.univ : Finset (Fin m → R)).image
      (fun f => -(1 + ∑ i, (f i : ℂ)))
    let U : Finset ℂ := R ∪ {1} ∪ W.biUnion (fun w => (Polynomial.nthRoots (m + 2) w).toFinset)
    apply Set.Finite.subset (Set.Finite.pi (t := fun _ => (U : Set ℂ)) (fun _ => U.finite_toSet))
    intro a ha
    rw [dc_mem_iff] at ha
    obtain ⟨hpen, hearly, hlast⟩ := ha
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    intro i
    induction i using Fin.lastCases with
    | last =>
      refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_,
        Finset.mem_image.2 ⟨fun i => ⟨a (Fin.castSucc (Fin.castSucc i)), (hRmem _).2 (hearly i)⟩,
          Finset.mem_univ _, rfl⟩, ?_⟩)
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
      exact hlast
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        rw [hpen]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self 1))
      | cast i =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _ ((hRmem _).2 (hearly i)))
  refine ⟨hfin, ?_⟩
  have hz : ∀ f : Fin m → R, ∃ z : ℂ, z ^ (m + 2) = -(1 + ∑ i, (f i : ℂ)) :=
    fun f => IsAlgClosed.exists_pow_nat_eq _ (by omega)
  choose z hz using hz
  let φ : (Fin m → R) → (Fin (m + 2) → ℂ) := fun f =>
    Fin.snoc (α := fun _ => ℂ) (Fin.snoc (α := fun _ => ℂ) (fun i => (f i : ℂ)) 1) (z f)
  have hφ : ∀ f, φ f ∈ polarSlice (m + 2) := by
    intro f
    rw [dc_mem_iff]
    simp only [φ, Fin.snoc_castSucc, Fin.snoc_last]
    exact ⟨trivial, fun i => (hRmem _).1 (f i).2, hz f⟩
  have hinj : Function.Injective φ := by
    intro f g hfg
    funext i
    have := congrFun hfg (Fin.castSucc (Fin.castSucc i))
    simp only [φ, Fin.snoc_castSucc] at this
    exact Subtype.ext this
  calc (m + 1) ^ m = Fintype.card (Fin m → R) := by
        simp [hRcard]
    _ = (Set.range φ).ncard := by
        rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
    _ ≤ (polarSlice (m + 2)).ncard :=
        Set.ncard_le_ncard (Set.range_subset_iff.2 hφ) hfin
