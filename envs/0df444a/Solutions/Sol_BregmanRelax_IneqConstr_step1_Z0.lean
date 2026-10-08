-- Prove2me | solution 1 for BregmanRelax.IneqConstr.step1_Z0
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:00:22.209052+00:00
-- url     : https://prove2.me/submissions/c21c580b-2b5f-4e84-afbe-0459f9aee8ae

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_IneqConstr_Program

set_option autoImplicit false

namespace C9e88395Aux

lemma grad_ineq {p : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfc : ConvexOn ℝ S f) (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    {x y : EuclideanSpace ℝ (Fin p)} (hx : x ∈ S) (hy : y ∈ S) :
    f x + inner ℝ (g x) (y - x) ≤ f y := by
  have hcv : ConvexOn ℝ (AffineMap.lineMap x y ⁻¹' S) (f ∘ AffineMap.lineMap x y) :=
    hfc.comp_affineMap _
  have h0 : (0:ℝ) ∈ (AffineMap.lineMap x y : ℝ → _) ⁻¹' S := by
    simpa [AffineMap.lineMap_apply_zero] using hx
  have h1 : (1:ℝ) ∈ (AffineMap.lineMap x y : ℝ → _) ⁻¹' S := by
    simpa [AffineMap.lineMap_apply_one] using hy
  have hF := hasGradientWithinAt_iff_hasFDerivWithinAt.mp (hfg x hx)
  have hL : HasDerivWithinAt (AffineMap.lineMap x y : ℝ → EuclideanSpace ℝ (Fin p)) (y - x)
      ((AffineMap.lineMap x y : ℝ → _) ⁻¹' S) 0 := AffineMap.hasDerivWithinAt_lineMap
  have hd := hF.comp_hasDerivWithinAt_of_eq (0:ℝ) hL (Set.mapsTo_preimage _ _)
    (by simp [AffineMap.lineMap_apply_zero])
  have := hcv.le_slope_of_hasDerivWithinAt h0 h1 zero_lt_one hd
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, InnerProductSpace.toDual_apply_apply, sub_zero, div_one] at this
  linarith

lemma grad_mono {p : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfc : ConvexOn ℝ S f) (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    {x y : EuclideanSpace ℝ (Fin p)} (hx : x ∈ S) (hy : y ∈ S) :
    0 ≤ inner ℝ (g y - g x) (y - x) := by
  have h1 := grad_ineq hfc hfg hx hy
  have h2 := grad_ineq hfc hfg hy hx
  have : inner ℝ (g y) (x - y) = - inner ℝ (g y) (y - x) := by
    rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]
  linarith

lemma sum_update {p m : ℕ} (u : Fin m → ℝ) (a : Fin m → EuclideanSpace ℝ (Fin p))
    (i : Fin m) (v : ℝ) :
    ∑ j, Function.update u i v j • a j = ∑ j, u j • a j + (v - u i) • a i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => u j • a j) (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, Function.update u i v j • a j
      = ∑ j ∈ Finset.univ.erase i, u j • a j :=
    Finset.sum_congr rfl (fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, Function.update_self, sub_smul]
  abel

end C9e88395Aux

open BregmanRelax.IneqConstr in
theorem solution {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (ha : ∀ i, a i ≠ 0)
    (hRne : (feasibleIneq a b S).Nonempty)
    (hA : BregmanRelax.Cyclic.DConditions (BregmanRelax.EqConstr.hyperplane a b) S (BregmanRelax.EqConstr.bregmanD f g) P)
    (h2 : BregmanRelax.EqConstr.Cond2 S (BregmanRelax.EqConstr.bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (hV : BregmanRelax.Cyclic.CondV S (BregmanRelax.EqConstr.bregmanD f g) (feasibleIneq a b S))
    (hm : 0 < m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (u : ℕ → Fin m → ℝ)
    (hx : IsMethodRun hm S g a b x u) :
    ∀ n, (∀ j, 0 ≤ u n j) ∧ g (x n) = ∑ j, u n j • a j := by
  obtain ⟨hx0, hu0, hg0, hstep⟩ := hx
  have hxS : ∀ n, x n ∈ S := by
    intro n
    cases n with
    | zero => exact interior_subset hx0
    | succ n => exact (hstep n).1
  intro n
  induction n with
  | zero => exact ⟨hu0, hg0⟩
  | succ n ih =>
    obtain ⟨ihu, ihg⟩ := ih
    obtain ⟨-, hcase⟩ := hstep n
    generalize (⟨n % m, Nat.mod_lt n hm⟩ : Fin m) = i at hcase
    rcases hcase with ⟨hlt, lam, hgx, hax, hu'⟩ | ⟨-, hx', hu'⟩ |
      ⟨-, -, μ', y, -, -, -, hgx, hu'⟩
    · have hmono := C9e88395Aux.grad_mono hfc.convexOn hfg (hxS n) (hxS (n + 1))
      rw [hgx, add_sub_cancel_left, real_inner_smul_left, inner_sub_right, hax] at hmono
      have hpos : 0 < b i - inner ℝ (a i) (x n) := by linarith
      have hlam : 0 ≤ lam := nonneg_of_mul_nonneg_left hmono hpos
      refine ⟨?_, ?_⟩
      · intro j
        rw [hu']
        by_cases hj : j = i
        · subst hj; simp; linarith [ihu j]
        · simp [Function.update_of_ne hj, ihu j]
      · rw [hgx, hu', C9e88395Aux.sum_update, ihg]
        congr 2
        ring
    · rw [hx', hu']; exact ⟨ihu, ihg⟩
    · refine ⟨?_, ?_⟩
      · intro j
        rw [hu']
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj, ihu j]
      · rw [hgx, hu', C9e88395Aux.sum_update, ihg]
        rw [show u n i - min μ' (u n i) - u n i = -min μ' (u n i) by ring, neg_smul,
          sub_eq_add_neg]
