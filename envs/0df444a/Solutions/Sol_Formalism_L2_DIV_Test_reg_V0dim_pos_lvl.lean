-- Prove2me | solution 1 for Formalism.L2.DIV.Test.reg_V0dim_pos_lvl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:30.056914+00:00
-- url     : https://prove2.me/submissions/1c2cb972-c3bc-49f8-997f-ed46bc8de442

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_I_actMat
import Theorems.Thm_Formalism_L2_DIV_Test_aug_eq_sum
import Theorems.Thm_Formalism_L2_DIV_Test_aug_idemOf_one
import Theorems.Thm_Formalism_L2_DIV_Test_aug_lvlIdem_one
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
end Formalism.L2.DIV
namespace Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
private theorem v0dim_pos_lemma (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G]
    [Fintype G] (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (h : ∑ t : G, (goodAt X P ψ).coeff t ≠ 0) : 0 < (regCSD K G).BaseDimension (regAct K G) X P ψ := by
  let f1 : (regCSD K G).Forms := ⟨fun _ => (1 : K), mem_regForms K G _⟩
  have hfix : ∀ t : G, regAct K G t f1 = f1 := fun t => rfl
  have hact : ∀ t : G, ((regCSD K G).actMat (regAct K G) t).mulVec ((regCSD K G).basis.equivFun f1) =
      (regCSD K G).basis.equivFun f1 := by
    intro t
    have h1 := (regCSD K G).I_actMat (regAct K G) t ((regCSD K G).basis.equivFun f1)
    rw [LinearEquiv.symm_apply_apply, hfix] at h1
    have h3 : (regCSD K G).basis.equivFun.symm (((regCSD K G).actMat (regAct K G) t).mulVec
        ((regCSD K G).basis.equivFun f1)) = f1 := Subtype.ext h1
    have h4 := congrArg (regCSD K G).basis.equivFun h3
    rwa [LinearEquiv.apply_symm_apply] at h4
  have hsm : ∀ (c : K) (M : Matrix (Fin (regCSD K G).dim) (Fin (regCSD K G).dim) K)
      (v : Fin (regCSD K G).dim → K), (c • M).mulVec v = c • M.mulVec v := by
    intro c M v
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hsum : ∀ (s : Finset G) (M : G → Matrix (Fin (regCSD K G).dim) (Fin (regCSD K G).dim) K)
      (v : Fin (regCSD K G).dim → K), (∑ t ∈ s, M t).mulVec v = ∑ t ∈ s, (M t).mulVec v := by
    intro s M v
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]
  have hga : ((regCSD K G).gaMat (regAct K G) (goodAt X P ψ)).mulVec ((regCSD K G).basis.equivFun f1) =
      (∑ t : G, (goodAt X P ψ).coeff t) • (regCSD K G).basis.equivFun f1 := by
    unfold CSD.gaMat
    rw [hsum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hsm, hact t]
  have hx1 : (regCSD K G).basis.equivFun f1 ≠ 0 := by
    intro h0
    have h5 : f1 = 0 := (regCSD K G).basis.equivFun.injective (by rw [h0, map_zero])
    have h6 := congrArg (fun f : (regCSD K G).Forms => (f : G → K) 1) h5
    simp [f1] at h6
  show 0 < Module.finrank K (LinearMap.range ((regCSD K G).gaMat (regAct K G) (goodAt X P ψ)).mulVecLin)
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨(∑ t : G, (goodAt X P ψ).coeff t) • (regCSD K G).basis.equivFun f1,
    LinearMap.mem_range.mpr ⟨(regCSD K G).basis.equivFun f1, by rw [Matrix.mulVecLin_apply, hga]⟩⟩, ?_⟩
  intro h0
  have h7 := congrArg Subtype.val h0
  exact smul_ne_zero h hx1 h7
end Formalism.L2.DIV.Test
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution (P : Subgroup G) :
    0 < (regCSD K G).BaseDimension (regAct K G) ({fun _ : G => (1 : K)} : Finset (G → K)) P 1 := by
  apply v0dim_pos_lemma
  rw [← aug_eq_sum]
  unfold goodAt
  rw [map_mul, aug_idemOf_one, aug_lvlIdem_one, mul_one]
  exact one_ne_zero
end Formalism.L2.DIV.Test
