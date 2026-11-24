-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.first_column_polynomials_characterize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.983376+00:00
-- url     : https://prove2.me/submissions/f7b4d975-be73-46d7-a011-32447c52d8b7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_CovWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
section general
variable {K : Type} [Field K] {r n : ℕ}
private lemma cw_pow_mem {ν : Fin n → ℕ} {y : MvPolynomial (Fin r × Fin n) K}
    (hy : y ∈ dualWeyl K r n ν) (k : ℕ) : y ^ k ∈ dualWeyl K r n (k • ν) := by
  induction k with
  | zero => simpa using (dualWeylMul K r n 0 0 0 0).2
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact (dualWeylMul K r n _ _ _ _).1 ih hy
private lemma cw_prod_mem {ι : Type} (s : Finset ι) (μ : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (h : ∀ i ∈ s, g i ∈ dualWeyl K r n (μ i)) :
    ∏ i ∈ s, g i ∈ dualWeyl K r n (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
private lemma cw_aeval_mem {σ : Type} {ν : Fin n → ℕ} (y : σ → MvPolynomial (Fin r × Fin n) K)
    (hy : ∀ i, y i ∈ dualWeyl K r n ν) (Q : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous Q) :
    aeval y f ∈ dualWeyl K r n (Q • ν) := by
  rw [aeval_def, eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = Q := by
    have := hf (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have := cw_prod_mem d.support (fun i => d i • ν) (fun i => y i ^ d i)
    (fun i _ => cw_pow_mem (hy i) _)
  rwa [← Finset.sum_smul, hdeg] at this
private lemma cw_prod_aeval {σ ι : Type} (y : σ → MvPolynomial (Fin r × Fin n) K) (s : Finset ι)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (e : ι → ℕ)
    (h : ∀ k, ∃ f : MvPolynomial σ K, f.IsHomogeneous (e k) ∧ aeval y f = g k) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous (∑ k ∈ s, e k) ∧ aeval y f = ∏ k ∈ s, g k := by
  choose f hf1 hf2 using h
  exact ⟨∏ k ∈ s, f k, IsHomogeneous.prod _ _ _ (fun k _ => hf1 k), by
    rw [map_prod]; exact Finset.prod_congr rfl fun k _ => hf2 k⟩
private lemma cw_span_le {σ : Type} (y : σ → MvPolynomial (Fin r × Fin n) K) (Q : ℕ) (ν : Fin n → ℕ)
    (h : ∀ (k : ℕ) (sz : Fin k → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
      shapeDeg sz = ν → ∃ f : MvPolynomial σ K, f.IsHomogeneous Q ∧ aeval y f = bideterminant K sz hsz I)
    (F : MvPolynomial (Fin r × Fin n) K) (hF : F ∈ dualWeyl K r n ν) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous Q ∧ aeval y f = F := by
  rw [standardMonomialSpanDomain K r n ν] at hF
  have key := (Submodule.span_le
    (p := Submodule.map (aeval y).toLinearMap (homogeneousSubmodule σ K Q))).mpr (by
      rintro _ ⟨k, sz, hsz, I, hs, rfl⟩
      obtain ⟨f, hf, hfe⟩ := h k sz hsz I hs
      exact ⟨f, hf, hfe⟩) hF
  obtain ⟨f, hf, hfe⟩ := key
  exact ⟨f, hf, hfe⟩
private lemma cw_single_mem (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin r) :
    initMinor K J hs ∈ dualWeyl K r n (fun t => if t.val < s then 1 else 0) := by
  have := bidetMem K r n 1 (fun _ => s) (fun _ => hs) (fun _ => J)
  have h1 : bideterminant K (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => J) = initMinor K J hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [h1, h2] at this
private lemma cw_minor0 (s : ℕ) (hs : s ≤ n) (h : s = 0) (J : Fin s → Fin r) :
    initMinor K J hs = 1 := by
  subst h
  simp [initMinor]
private lemma cw_le_of_shape {k : ℕ} (sz : Fin k → ℕ) (t : Fin n) (h : shapeDeg sz t = 0) (j : Fin k) :
    sz j ≤ t.val := by
  by_contra hk
  have hm : j ∈ Finset.univ.filter (fun k => t.val < sz k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  simp only [shapeDeg, Finset.card_eq_zero] at h
  rw [h] at hm
  simp at hm
end general
private lemma cw_card {n k : ℕ} (sz : Fin k → ℕ) :
    ∑ j, (if 0 < sz j then 1 else 0) = shapeDeg sz (0 : Fin (n + 1)) := by
  simp only [shapeDeg, Fin.val_zero, Finset.sum_boole, Nat.cast_id]
  congr
private lemma cw_minor1 {K : Type} [Field K] {r n : ℕ} (s : ℕ) (hs : s ≤ n + 1) (h : 0 < s) (h1 : s ≤ 1)
    (J : Fin s → Fin r) : initMinor K J hs = X (J ⟨0, h⟩, 0) := by
  obtain rfl : s = 1 := by omega
  simp [initMinor]
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
theorem _root_.solution : FirstColumnPolynomialsSpan := by
  intro K _ m P F hm
  have hren : ∀ f : MvPolynomial (Fin (m + 1)) K, rename (fun i => (i, (0 : Fin (m + 1)))) f =
      aeval (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) f :=
    fun f => DFunLike.congr_fun (algHom_ext fun i => by simp) f
  simp only [hren]
  constructor
  · refine cw_span_le _ P _ ?_ F
    intro k sz hsz I hs
    have h0 : shapeDeg sz (0 : Fin (m + 1)) = P := by rw [hs]; simp
    have h1 : shapeDeg sz (⟨1, by omega⟩ : Fin (m + 1)) = 0 := by rw [hs]; simp [Fin.ext_iff]
    have hle : ∀ j, sz j ≤ 1 := cw_le_of_shape sz _ h1
    have := cw_prod_aeval
      (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) Finset.univ
      (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_
    · rw [cw_card, h0] at this
      exact this
    · intro j
      by_cases hj : 0 < sz j
      · refine ⟨X (I j ⟨0, hj⟩), by simpa [hj] using isHomogeneous_X K (I j ⟨0, hj⟩), ?_⟩
        rw [aeval_X, cw_minor1 _ _ hj (hle j)]
      · exact ⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K,
          by rw [map_one, cw_minor0 _ _ (by omega)]⟩
  · rintro ⟨f, hf, rfl⟩
    have := cw_aeval_mem
      (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (ν := fun t => if t.val < 1 then 1 else 0) ?_ P f hf
    · convert this using 2
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · simp [ht]
    · intro i
      have := cw_single_mem (K := K) (r := m + 1) (n := m + 1) 1 (by omega) (fun _ => i)
      rwa [cw_minor1 _ _ (by omega) le_rfl] at this
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
