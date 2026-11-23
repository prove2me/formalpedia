-- Prove2me | solution 1 for Formalism.L2.DIV.map_injective_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:21.272848+00:00
-- url     : https://prove2.me/submissions/4b570926-2097-4f6d-bf32-8a8650edaad0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.L2.DIV
open Formalism.DivisionValues
section Sub
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
end Sub
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
namespace CSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)
end CSD
section Basic
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Basic
section Lvl
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Lvl
section Roots
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G]
end Roots
section Chars
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Chars
section Conj
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
end Conj
section Assemble
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
end Assemble
section Schur
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
end Schur
private theorem exists_mul_lemma {K : Type} [Field K] {m n p : ℕ} {A : Matrix (Fin m) (Fin n) K}
    {B : Matrix (Fin m) (Fin p) K}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    ∃ C : Matrix (Fin n) (Fin p) K, B = A * C := by
  have hc : ∀ j, ∃ c : Fin n → K, A.mulVec c = fun i => B i j := by
    intro j
    have hB : (fun i => B i j) ∈ LinearMap.range B.mulVecLin :=
      LinearMap.mem_range.mpr ⟨Pi.single j 1, by
        ext i
        simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (h hB)
    exact ⟨c, by rw [← Matrix.mulVecLin_apply]; exact hc⟩
  choose c hc using hc
  refine ⟨Matrix.of fun k j => c j k, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact this.symm
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
end Formalism.L2.DIV.Test
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective E.mulVec) (σ : K →+* ℂ) : Function.Injective (E.map σ).mulVec := by
  have hE' : Function.Injective E.mulVecLin := hE
  have hrk : E.rank = d := by
    unfold Matrix.rank
    rw [LinearMap.finrank_range_of_inj hE', Module.finrank_fin_fun]
  have hrkT : Eᵀ.rank = d := by rw [Matrix.rank_transpose, hrk]
  have htop : LinearMap.range Eᵀ.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrkT
  obtain ⟨C, hC⟩ := exists_mul_lemma (A := Eᵀ) (B := (1 : Matrix (Fin d) (Fin d) K))
    (by rw [htop]; exact le_top)
  have hL : Cᵀ * E = 1 := by
    have := congrArg Matrix.transpose hC
    rwa [Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose, eq_comm] at this
  have hLσ : Cᵀ.map σ * E.map σ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have := congrArg (fun z => (Cᵀ.map σ).mulVec z) hxy
  simp only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] at this
  exact this
end Formalism.L2.DIV
