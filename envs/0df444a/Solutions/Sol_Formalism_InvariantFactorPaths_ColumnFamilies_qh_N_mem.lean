-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:34.799971+00:00
-- url     : https://prove2.me/submissions/53cd70b5-3676-4e12-976a-bd524cdfbb39

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_castLE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mem_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) :
    qhN R s hs J ∈ inducedSections R (fun a : Fin n => if a.val < s then 1 else 0) := by
  have qh_sum_castLE {M : Type} [AddCommMonoid M] {s n : ℕ} (hs : s ≤ n) (F : Fin n → M)
      (h : ∀ a : Fin n, s ≤ a.val → F a = 0) : ∑ a' : Fin s, F (Fin.castLE hs a') = ∑ a, F a := by
    have h1 : ∑ a' : Fin s, F (Fin.castLE hs a') = ∑ a ∈ (univ : Finset (Fin s)).map (Fin.castLEEmb hs), F a := by
      rw [Finset.sum_map]; rfl
    rw [h1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    apply h
    by_contra hlt
    push Not at hlt
    exact ha (Finset.mem_map.2 ⟨⟨a.val, hlt⟩, Finset.mem_univ _, by ext; rfl⟩)
  rw [qh_mem_iff]
  intro R' _ _ b g u hb hu
  rw [qh_evGLR_N, qh_evGLR_N]
  have h1 : (Matrix.of fun p q : Fin s => (b * g).val (Fin.castLE hs p) (J q)) =
      (Matrix.of fun p q : Fin s => b.val (Fin.castLE hs p) (Fin.castLE hs q)) *
        (Matrix.of fun p q : Fin s => g.val (Fin.castLE hs p) (J q)) := by
    ext p q
    rw [Units.val_mul, Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]
    symm
    apply qh_sum_castLE hs (fun a => b.val (Fin.castLE hs p) a * g.val a (J q))
    intro a ha
    rw [hb _ _ (by rw [Fin.lt_def]; simp; omega), zero_mul]
  have h2 : (Matrix.of fun p q : Fin s => b.val (Fin.castLE hs p) (Fin.castLE hs q)).det =
      ∏ p : Fin s, b.val (Fin.castLE hs p) (Fin.castLE hs p) :=
    Matrix.det_of_isLowerTriangular _ (fun i j hij => hb _ _ (by rw [Fin.lt_def]; simpa using hij))
  rw [h1, Matrix.det_mul, h2]
  congr 1
  simp only [← hu]
  have h3 : ∀ a : Fin n, ((u a ^ (if a.val < s then (1 : ℤ) else 0) : R'ˣ) : R') =
      if a.val < s then (u a : R') else 1 := by
    intro a; split_ifs <;> simp
  rw [Units.coe_prod]
  simp only [h3]
  rw [← qh_prod_castLE hs (fun a : Fin n => if a.val < s then (u a : R') else 1)
    (fun a ha => if_neg (by omega))]
  apply Finset.prod_congr rfl
  intro p _
  simp
end Formalism.InvariantFactorPaths.ColumnFamilies
