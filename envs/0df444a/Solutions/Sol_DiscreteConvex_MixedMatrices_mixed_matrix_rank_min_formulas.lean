-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.mixed_matrix_rank_min_formulas
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:14.79206+00:00
-- url     : https://prove2.me/submissions/e9196b4c-b9b2-44f8-b699-02dcf27a7501

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun
import Theorems.Thm_DiscreteConvex_MixedMatrices_exists_tight_pair
import Theorems.Thm_DiscreteConvex_MixedMatrices_rank_le_matrixSubRank_add
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_le_gammaFun
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_eq_zero_iff
import Theorems.Thm_DiscreteConvex_MixedMatrices_gammaFun_eq_zero_iff

set_option autoImplicit false

namespace Dca14C5

open DiscreteConvex.MixedMatrices

variable {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F] [Algebra K F]
  [DecidableEq R] [DecidableEq C]

/-- Weak duality for the first formula, in `ℤ` (so it can be fed to `Finset.le_inf'`). -/
theorem pk_wd_tau {A : Matrix R C F} {Q : Matrix R C K} {T : Matrix R C F}
    (hA : IsMixedMatrix A Q T) (I : Finset R) (J : Finset C) :
    (A.rank : ℤ) - Fintype.card R - Fintype.card C ≤
      (MatrixSubRank Q I J : ℤ) + (MatrixSubRank T I J : ℤ) - I.card - J.card := by
  have h := rank_le_matrixSubRank_add A Q T hA.1 I J
  have h1 := Finset.card_add_card_compl I
  have h2 := Finset.card_add_card_compl J
  omega

/-- Weak duality for the second formula: `τ ≤ γ`. -/
theorem pk_wd_gamma {A : Matrix R C F} {Q : Matrix R C K} {T : Matrix R C F}
    (hA : IsMixedMatrix A Q T) (I : Finset R) (J : Finset C) :
    (A.rank : ℤ) - Fintype.card R - Fintype.card C ≤
      (MatrixSubRank Q I J : ℤ) + (GammaFun T I J : ℤ) - I.card - J.card := by
  have h := pk_wd_tau hA I J
  have h' := matrixSubRank_le_gammaFun T I J
  omega

/-- Weak duality on a pair with `γ(I,J) = 0` (so `T[I,J] = 0` and `τ = 0`). -/
theorem pk_wd_zero {A : Matrix R C F} {Q : Matrix R C K} {T : Matrix R C F}
    (hA : IsMixedMatrix A Q T) {I : Finset R} {J : Finset C} (hγ : GammaFun T I J = 0) :
    (A.rank : ℤ) - Fintype.card R - Fintype.card C ≤
      (MatrixSubRank Q I J : ℤ) - I.card - J.card := by
  have hτ : MatrixSubRank T I J = 0 :=
    (matrixSubRank_eq_zero_iff T I J).2 ((gammaFun_eq_zero_iff T I J).1 hγ)
  have h := pk_wd_tau hA I J
  omega

/-- Casting a `ℤ`-valued difference into `WithTop ℤ` (with `ℕ`-casts on the subtrahends). -/
theorem pk_coe_sub (a : ℤ) (n k : ℕ) :
    ((a : ℤ) : WithTop ℤ) - (n : WithTop ℤ) - (k : WithTop ℤ) = ((a - n - k : ℤ) : WithTop ℤ) := by
  norm_cast

end Dca14C5

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    ((A.rank : ℤ) =
        (Finset.univ : Finset (Finset R × Finset C)).inf' Finset.univ_nonempty
          (fun p => (MatrixSubRank Q p.1 p.2 : ℤ) + (MatrixSubRank T p.1 p.2 : ℤ) -
            p.1.card - p.2.card) +
          Fintype.card R + Fintype.card C) ∧
      ((A.rank : ℤ) =
        (Finset.univ : Finset (Finset R × Finset C)).inf' Finset.univ_nonempty
          (fun p => (MatrixSubRank Q p.1 p.2 : ℤ) + (GammaFun T p.1 p.2 : ℤ) -
            p.1.card - p.2.card) +
          Fintype.card R + Fintype.card C) ∧
      ((A.rank : WithTop ℤ) =
        (Finset.univ : Finset (Finset R × Finset C)).inf
            (fun p => if GammaFun T p.1 p.2 = 0
                      then ((MatrixSubRank Q p.1 p.2 : ℤ) - p.1.card - p.2.card : WithTop ℤ)
                      else ⊤) +
          (Fintype.card R : WithTop ℤ) + (Fintype.card C : WithTop ℤ)) := by
  obtain ⟨I₀, J₀, hτ₀, hρ₀⟩ := exists_tight_pair A Q T hA
  have hc1 := Finset.card_add_card_compl I₀
  have hc2 := Finset.card_add_card_compl J₀
  have hγ₀ : GammaFun T I₀ J₀ = 0 :=
    (gammaFun_eq_zero_iff T I₀ J₀).2 ((matrixSubRank_eq_zero_iff T I₀ J₀).1 hτ₀)
  refine ⟨?_, ?_, ?_⟩
  · have h : (Finset.univ : Finset (Finset R × Finset C)).inf' Finset.univ_nonempty
        (fun p => (MatrixSubRank Q p.1 p.2 : ℤ) + (MatrixSubRank T p.1 p.2 : ℤ) -
          p.1.card - p.2.card) = (A.rank : ℤ) - Fintype.card R - Fintype.card C := by
      apply le_antisymm
      · refine (Finset.inf'_le _ (Finset.mem_univ (I₀, J₀))).trans ?_
        simp only
        omega
      · exact Finset.le_inf' _ _ fun p _ => Dca14C5.pk_wd_tau hA p.1 p.2
    omega
  · have h : (Finset.univ : Finset (Finset R × Finset C)).inf' Finset.univ_nonempty
        (fun p => (MatrixSubRank Q p.1 p.2 : ℤ) + (GammaFun T p.1 p.2 : ℤ) -
          p.1.card - p.2.card) = (A.rank : ℤ) - Fintype.card R - Fintype.card C := by
      apply le_antisymm
      · refine (Finset.inf'_le _ (Finset.mem_univ (I₀, J₀))).trans ?_
        simp only
        omega
      · exact Finset.le_inf' _ _ fun p _ => Dca14C5.pk_wd_gamma hA p.1 p.2
    omega
  · have h : (Finset.univ : Finset (Finset R × Finset C)).inf
        (fun p => if GammaFun T p.1 p.2 = 0
                  then ((MatrixSubRank Q p.1 p.2 : ℤ) - p.1.card - p.2.card : WithTop ℤ)
                  else ⊤) =
        (((A.rank : ℤ) - Fintype.card R - Fintype.card C : ℤ) : WithTop ℤ) := by
      apply le_antisymm
      · refine (Finset.inf_le (Finset.mem_univ (I₀, J₀))).trans ?_
        simp only [hγ₀, if_true]
        rw [Dca14C5.pk_coe_sub]
        exact WithTop.coe_le_coe.2 (by omega)
      · refine Finset.le_inf fun p _ => ?_
        by_cases hγ : GammaFun T p.1 p.2 = 0
        · simp only [hγ, if_true]
          rw [Dca14C5.pk_coe_sub]
          exact WithTop.coe_le_coe.2 (Dca14C5.pk_wd_zero hA hγ)
        · simp only [hγ, if_false]
          exact le_top
    rw [h, ← WithTop.coe_natCast (α := ℤ) (Fintype.card R),
      ← WithTop.coe_natCast (α := ℤ) (Fintype.card C), ← WithTop.coe_natCast (α := ℤ) A.rank,
      ← WithTop.coe_add, ← WithTop.coe_add]
    exact WithTop.coe_inj.2 (by omega)

#print axioms solution
