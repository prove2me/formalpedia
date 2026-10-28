-- Prove2me | solution 1 for DiffNeighbors.Bias.taylor_remainder
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T07:04:09.006381+00:00
-- url     : https://prove2.me/submissions/3dc90f3e-d53b-4a71-9c90-98c09900aeed

import Definitions.Def_DiffNeighbors_Bias_Model
import Init
import Mathlib


section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def ownOutcome (i : ι) (z : ι → Bool) : ℝ := ind (z i)

theorem own_neighborhood (G : SimpleGraph ι) : NeighborhoodInterference G (@ownOutcome ι) := by
  intro i z z' h
  simp only [ownOutcome,h i (Or.inl rfl)]

theorem own_conditional (i : ι) (a : Bool) : condOutcome (@ownOutcome ι) i a = fun _ => ind a := by
  funext z
  simp [condOutcome,ownOutcome]

theorem own_smooth (i : ι) (a : Bool) : IsSmooth 0 (condOutcome (@ownOutcome ι) i a) := by
  rw [own_conditional]
  intro z j k
  simp [secondDiff]

theorem estimator_formula_correct (G : SimpleGraph ι) [DecidableRel G.Adj] (p : ℝ)
    (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    dnEstimator G p f z = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, eta p z i * ((∑ j ∈ G.neighborFinset i, f j z * xi p z j) + f i z) := rfl

theorem empty_estimator (p : ℝ) (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    dnEstimator (⊥ : SimpleGraph ι) p f z = (Fintype.card ι : ℝ)⁻¹ * ∑ i, eta p z i * f i z := by
  simp [dnEstimator]

theorem singleton_ate [Unique ι] : ate (@ownOutcome ι) = 1 := by
  simp [ate,ownOutcome,ind]

theorem bernExp_const (p c : ℝ) : bernExp (ι:=ι) p (fun _ => c) = c := by
  unfold bernExp mlExt
  rw [← Finset.sum_mul, ← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1-p)]
  have h : (∑ b : Bool, if b then p else 1-p) = 1 := by simp [Fintype.sum_bool]
  simp [h]

end Queelius.NetworkInterference

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem neighbor_sum_swap (G : SimpleGraph ι) [DecidableRel G.Adj] (F : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ G.neighborFinset i, F i j) = ∑ i, ∑ j ∈ G.neighborFinset i, F j i := by
  simp only [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [G.adj_comm]

end Queelius.NetworkInterference

namespace DiffNeighbors.Bias
open Finset
theorem credit_assignment {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (p : ℝ) (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    dnEstimator G p f z = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (eta p z i + xi p z i * ∑ j ∈ G.neighborFinset i, eta p z j) * f i z := by
  unfold dnEstimator
  congr 1
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,add_mul,Finset.sum_mul]
  rw [Queelius.NetworkInterference.neighbor_sum_swap G]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem bernoulli_weights_sum (w : ι → ℝ) :
    ∑ z : ι → Bool, ∏ j, (if z j then w j else 1-w j) = 1 := by
  rw [← Fintype.prod_sum (fun j (b : Bool) => if b then w j else 1-w j)]
  simp

theorem bernoulli_weight_nonnegative (w : ι → ℝ) (hw : ∀ j, w j ∈ Set.Icc (0 : ℝ) 1)
    (z : ι → Bool) : 0 ≤ ∏ j, (if z j then w j else 1-w j) := by
  apply Finset.prod_nonneg
  intro j hj
  split_ifs
  · exact (hw j).1
  · exact sub_nonneg.mpr (hw j).2

theorem mlExt_const (w : ι → ℝ) (c : ℝ) : mlExt (ι:=ι) (fun _ => c) w = c := by
  unfold mlExt
  rw [← Finset.sum_mul,bernoulli_weights_sum,one_mul]

theorem mlExt_abs_bound (h : (ι → Bool) → ℝ) (w : ι → ℝ)
    (hw : ∀ j, w j ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : ∀ z, |h z| ≤ ε) :
    |mlExt h w| ≤ ε := by
  unfold mlExt
  calc
    _ ≤ ∑ z : ι → Bool, |(∏ j, if z j then w j else 1-w j) * h z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : ι → Bool, (∏ j, if z j then w j else 1-w j) * ε := by
      apply Finset.sum_le_sum
      intro z hz
      rw [abs_mul,abs_of_nonneg (bernoulli_weight_nonnegative w hw z)]
      exact mul_le_mul_of_nonneg_left (hε z) (bernoulli_weight_nonnegative w hw z)
    _ = ε := by rw [← Finset.sum_mul,bernoulli_weights_sum,one_mul]

theorem treatment_square_le_one (a : Bool) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (ind a - p)^2 ≤ 1 := by
  cases a <;> simp only [ind,Bool.false_eq_true,if_false,if_true] <;> nlinarith [hp.1,hp.2,mul_nonneg hp.1 (sub_nonneg.mpr hp.2)]

end Queelius.NetworkInterference

namespace DiffNeighbors.Bias
open Finset
theorem remainder_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (f : ι → (ι → Bool) → ℝ) (i : ι) (a : Bool) (ε p : ℝ) (w : ι → ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ l, w l ∈ Set.Icc (0 : ℝ) 1)
    (hε : IsSmooth ε (condOutcome f i a)) :
    |∑ j ∈ G.neighborFinset i, ∑ k ∈ (G.neighborFinset i).erase j,
        (ind a - p) ^ 2 * mlExt (fun z => secondDiff (condOutcome f i a) j k z) w|
      ≤ (G.maxDegree : ℝ) ^ 2 * ε := by
  have he : 0 ≤ ε := le_trans (abs_nonneg _) (hε (fun _ => false) i i)
  have hc := Queelius.NetworkInterference.treatment_square_le_one a p hp
  have hb (j k : ι) : |(ind a-p)^2 * mlExt (fun z => secondDiff (condOutcome f i a) j k z) w| ≤ ε := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (ind a-p)^2 * ε := mul_le_mul_of_nonneg_left
        (Queelius.NetworkInterference.mlExt_abs_bound _ w hw ε (fun z => hε z j k)) (sq_nonneg _)
      _ ≤ ε := mul_le_of_le_one_left he hc
  calc
    _ ≤ ∑ j ∈ G.neighborFinset i, ∑ k ∈ (G.neighborFinset i).erase j,
        |(ind a-p)^2 * mlExt (fun z => secondDiff (condOutcome f i a) j k z) w| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j hj => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ j ∈ G.neighborFinset i, ∑ k ∈ (G.neighborFinset i).erase j, ε :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hb j k))
    _ ≤ ∑ j ∈ G.neighborFinset i, ∑ k ∈ G.neighborFinset i, ε := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun k hk hnot => he)
    _ = ((G.neighborFinset i).card : ℝ)^2 * ε := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ (G.maxDegree : ℝ)^2 * ε := by
      apply mul_le_mul_of_nonneg_right _ he
      have hd : ((G.neighborFinset i).card : ℝ) ≤ G.maxDegree := by
        exact_mod_cast G.degree_le_maxDegree i
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem bernExp_singleton [Unique ι] (p : ℝ) (h : (ι → Bool) → ℝ) :
    bernExp p h = (1-p) * h (fun _ => false) + p * h (fun _ => true) := by
  unfold bernExp mlExt
  rw [← (Equiv.funUnique ι Bool).symm.sum_comp
    (fun z => (∏ j, if z j then p else 1-p) * h z)]
  simp [Fintype.sum_bool,Equiv.funUnique_symm_apply,add_comm]
  have hc (b : Bool) : (uniqueElim b : ι → Bool) = fun _ => b := by
    funext i
    cases Unique.eq_default i
    rfl
  rw [hc,hc]
  ring

theorem actual_singleton_expectation [Unique ι] (p : ℝ) (hp : p ≠ 0) :
    bernExp p (dnEstimator (⊥ : SimpleGraph ι) p ownOutcome) = 1 := by
  rw [bernExp_singleton]
  simp [dnEstimator,eta,ownOutcome,ind,hp]

theorem actual_singleton_unbiased [Unique ι] :
    bernExp (1/2) (dnEstimator (⊥ : SimpleGraph ι) (1/2) ownOutcome) = ate (@ownOutcome ι) := by
  rw [actual_singleton_expectation (1/2) (by norm_num),singleton_ate]

/-- Deliberately wrong negative control. This is not the platform estimator. -/
def misgroupedEstimator (G : SimpleGraph ι) [DecidableRel G.Adj] (p : ℝ)
    (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, eta p z i *
    (∑ j ∈ G.neighborFinset i, (f j z * xi p z j + f i z))

theorem misgrouped_empty (p : ℝ) (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    misgroupedEstimator (⊥ : SimpleGraph ι) p f z = 0 := by
  simp [misgroupedEstimator]

theorem misgrouped_bias [Unique ι] :
    |ate (@ownOutcome ι) - bernExp (1/2) (misgroupedEstimator (⊥ : SimpleGraph ι) (1/2) ownOutcome)| = 1 := by
  simp [singleton_ate,bernExp,mlExt,misgrouped_empty]

theorem misgrouped_error_identity (G : SimpleGraph ι) [DecidableRel G.Adj] (p : ℝ)
    (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    misgroupedEstimator G p f z - dnEstimator G p f z =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, eta p z i * (((G.neighborFinset i).card : ℝ) - 1) * f i z := by
  unfold misgroupedEstimator dnEstimator
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
  ring

end Queelius.NetworkInterference

end

section
open DiffNeighbors.Bias in
theorem submission_primary_solution {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (p : ℝ) (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    dnEstimator G p f z = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (eta p z i + xi p z i * ∑ j ∈ G.neighborFinset i, eta p z j) * f i z :=
  credit_assignment G p f z

end

section
noncomputable section
namespace Queelius.NetworkInterference.Controls
open DiffNeighbors.Bias Finset

def pairOutcome (_ : Fin 3) (z : Fin 3 → Bool) : ℝ := ind (z 0) * ind (z 1)

theorem pair_second (j k : Fin 3) :
    secondDiff (condOutcome pairOutcome 2 true) j k =
      fun _ => if (j=0 ∧ k=1) ∨ (j=1 ∧ k=0) then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> funext z <;>
    norm_num [secondDiff,condOutcome,pairOutcome,Function.update_apply,ind,Fin.ext_iff] <;> ring

theorem pair_smooth : IsSmooth 1 (condOutcome pairOutcome 2 true) := by
  intro z j k
  rw [pair_second]
  split_ifs <;> norm_num

theorem triangle_degree : (⊤ : SimpleGraph (Fin 3)).maxDegree = 2 := by decide

theorem nonzero_remainder :
    (∑ j ∈ (⊤ : SimpleGraph (Fin 3)).neighborFinset 2,
      ∑ k ∈ ((⊤ : SimpleGraph (Fin 3)).neighborFinset 2).erase j,
        (ind true - (0 : ℝ))^2 *
          mlExt (fun z => secondDiff (condOutcome pairOutcome 2 true) j k z) (fun _ => 1/2)) = 2 := by
  have hN : (⊤ : SimpleGraph (Fin 3)).neighborFinset 2 = {0,1} := by decide
  rw [hN]
  simp only [pair_second,mlExt_const]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  norm_num [ind,h01,Ne.symm h01]
  have h1 : ({x ∈ ({1} : Finset (Fin 3)) | x = 1}).card = 1 := by decide
  have h2 : ({x ∈ ({0,1} : Finset (Fin 3)).erase 1 | x = 0}).card = 1 := by decide
  rw [h1,h2]
  norm_num

theorem nonzero_bound_checked :
    |(∑ j ∈ (⊤ : SimpleGraph (Fin 3)).neighborFinset 2,
      ∑ k ∈ ((⊤ : SimpleGraph (Fin 3)).neighborFinset 2).erase j,
        (ind true - (0 : ℝ))^2 *
          mlExt (fun z => secondDiff (condOutcome pairOutcome 2 true) j k z) (fun _ => 1/2))|
        ≤ ((⊤ : SimpleGraph (Fin 3)).maxDegree : ℝ)^2 * 1 := by
  exact remainder_bound _ pairOutcome 2 true 1 0 (fun _ => 1/2)
    (by norm_num) (by intro l; norm_num) pair_smooth

end Queelius.NetworkInterference.Controls

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def insertCoord (j : ι) (b : Bool) (r : {k : ι // k ≠ j} → Bool) : ι → Bool :=
  (Equiv.funSplitAt j Bool).symm (b,r)

@[simp] theorem insertCoord_at (j : ι) (b : Bool) (r : {k : ι // k ≠ j} → Bool) :
    insertCoord j b r j = b := by simp [insertCoord]

@[simp] theorem insertCoord_other (j : ι) (b : Bool) (r : {k : ι // k ≠ j} → Bool)
    (k : {k : ι // k ≠ j}) : insertCoord j b r k = r k := by
  simp [insertCoord,k.property]

@[simp] theorem update_insertCoord (j : ι) (b a : Bool) (r : {k : ι // k ≠ j} → Bool) :
    Function.update (insertCoord j b r) j a = insertCoord j a r := by
  ext k
  by_cases hk : k = j
  · subst k; simp
  · simp [insertCoord,Equiv.funSplitAt_symm_apply,Function.update_of_ne hk,hk]

theorem weight_insertCoord (w : ι → ℝ) (j : ι) (b : Bool)
    (r : {k : ι // k ≠ j} → Bool) :
    (∏ k, if insertCoord j b r k then w k else 1-w k) =
      (if b then w j else 1-w j) * ∏ k : {k : ι // k ≠ j}, if r k then w k else 1-w k := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [insertCoord_at]
  congr 1
  rw [Finset.prod_subtype (p := fun k => k ≠ j) (univ.erase j) (by simp)]
  apply Finset.prod_congr rfl
  intro k hk
  simp

def sliceExp (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) (b : Bool) : ℝ :=
  mlExt (fun r => h (insertCoord j b r)) (fun k : {k : ι // k ≠ j} => w k)

theorem mlExt_split (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) :
    mlExt h w = (1-w j) * sliceExp h w j false + w j * sliceExp h w j true := by
  unfold mlExt
  rw [← (Equiv.funSplitAt j Bool).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ b : Bool, ∑ r : {k : ι // k ≠ j} → Bool,
    (∏ k, if insertCoord j b r k then w k else 1-w k) * h (insertCoord j b r)) = _
  simp only [weight_insertCoord]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  simp only [mul_assoc,← Finset.mul_sum]
  exact add_comm _ _

theorem mlExt_condition (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) (b : Bool) :
    mlExt (fun z => h (Function.update z j b)) w = sliceExp h w j b := by
  rw [mlExt_split _ _ j]
  simp only [sliceExp,update_insertCoord]
  ring

@[simp] theorem sliceExp_update (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) (b : Bool) (t : ℝ) :
    sliceExp h (Function.update w j t) j b = sliceExp h w j b := by
  unfold sliceExp
  congr 1
  funext k
  exact Function.update_of_ne k.property t w

theorem mlExt_update (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) (t : ℝ) :
    mlExt h (Function.update w j t) =
      (1-t) * mlExt (fun z => h (Function.update z j false)) w +
      t * mlExt (fun z => h (Function.update z j true)) w := by
  rw [mlExt_split _ _ j]
  simp [mlExt_condition]

end Queelius.NetworkInterference

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem mlExt_add (f g : (ι → Bool) → ℝ) (w : ι → ℝ) :
    mlExt (fun z => f z + g z) w = mlExt f w + mlExt g w := by
  simp [mlExt,mul_add,Finset.sum_add_distrib]

theorem mlExt_sub (f g : (ι → Bool) → ℝ) (w : ι → ℝ) :
    mlExt (fun z => f z - g z) w = mlExt f w - mlExt g w := by
  simp [mlExt,mul_sub,Finset.sum_sub_distrib]

theorem mlExt_smul (c : ℝ) (f : (ι → Bool) → ℝ) (w : ι → ℝ) :
    mlExt (fun z => c * f z) w = c * mlExt f w := by
  simp only [mlExt,mul_left_comm _ c,Finset.mul_sum]

theorem mlExt_sum {κ : Type v} (s : Finset κ) (f : κ → (ι → Bool) → ℝ) (w : ι → ℝ) :
    mlExt (fun z => ∑ k ∈ s, f k z) w = ∑ k ∈ s, mlExt (f k) w := by
  simp only [mlExt,Finset.mul_sum]
  exact Finset.sum_comm

theorem mlExt_indicator (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) (b : Bool) :
    mlExt (fun z => (if z j = b then (1 : ℝ) else 0) * h z) w =
      bernProb (w j) b * mlExt (fun z => h (Function.update z j b)) w := by
  rw [mlExt_split _ _ j,mlExt_condition]
  cases b <;> simp [sliceExp,mlExt,bernProb]

theorem mlExt_propensity (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) (b : Bool)
    (hb : bernProb (w j) b ≠ 0) :
    mlExt (fun z => (if z j = b then (1 : ℝ) else 0) / bernProb (w j) b * h z) w =
      mlExt (fun z => h (Function.update z j b)) w := by
  have hf : (fun z => (if z j = b then (1 : ℝ) else 0) / bernProb (w j) b * h z) =
      (fun z => (bernProb (w j) b)⁻¹ * ((if z j = b then (1 : ℝ) else 0) * h z)) := by
    funext z; ring
  rw [hf,mlExt_smul,mlExt_indicator]
  field_simp

end Queelius.NetworkInterference

end

section
noncomputable section
namespace DiffNeighbors.Bias
open Finset Queelius.NetworkInterference

theorem first_partial {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → Bool) → ℝ) (w : ι → ℝ)
    (j : ι) :
    HasDerivAt (fun t => mlExt h (Function.update w j t))
      (mlExt (fun z => h (Function.update z j true)) w
        - mlExt (fun z => h (Function.update z j false)) w) (w j) := by
  let A := mlExt (fun z => h (Function.update z j false)) w
  let B := mlExt (fun z => h (Function.update z j true)) w
  have hd := ((hasDerivAt_id (w j)).const_mul (B-A)).add_const A
  have heq : (fun t => mlExt h (Function.update w j t)) = (fun t => (B-A)*t+A) := by
    funext t
    rw [mlExt_update]
    dsimp [A,B]
    ring
  rw [heq]
  simpa only [id_eq,mul_one] using hd

theorem second_partial {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → Bool) → ℝ) (w : ι → ℝ)
    (j : ι) :
    (∀ k, j ≠ k →
      HasDerivAt (fun t => mlExt (fun z => h (Function.update z j true)) (Function.update w k t)
          - mlExt (fun z => h (Function.update z j false)) (Function.update w k t))
        (mlExt (fun z => secondDiff h j k z) w) (w k)) ∧
    HasDerivAt (fun t => mlExt (fun z => h (Function.update z j true)) (Function.update w j t)
        - mlExt (fun z => h (Function.update z j false)) (Function.update w j t))
      0 (w j) := by
  constructor
  · intro k hjk
    convert (first_partial (fun z => h (Function.update z j true)) w k).sub
      (first_partial (fun z => h (Function.update z j false)) w k) using 1 <;> try rfl
    simp only [secondDiff,mlExt_add,mlExt_sub]
    simp only [Function.update_comm hjk]
    ring
  · convert (first_partial (fun z => h (Function.update z j true)) w j).sub
      (first_partial (fun z => h (Function.update z j false)) w j) using 1 <;> try rfl
    simp only [Function.update_idem]
    ring

end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem mlExt_two_propensity (h : (ι → Bool) → ℝ) (w : ι → ℝ) (i j : ι) (hji : j ≠ i)
    (a b : Bool) (ha : bernProb (w i) a ≠ 0) (hb : bernProb (w j) b ≠ 0) :
    mlExt (fun z => (if z i = a then (1 : ℝ) else 0) / bernProb (w i) a *
      ((if z j = b then (1 : ℝ) else 0) / bernProb (w j) b) * h z) w =
    mlExt (fun z => h (Function.update (Function.update z j b) i a)) w := by
  calc
    _ = mlExt (fun z => (if z j = b then (1 : ℝ) else 0) / bernProb (w j) b *
          ((if z i = a then (1 : ℝ) else 0) / bernProb (w i) a * h z)) w := by
      congr 1; funext z; ring
    _ = mlExt (fun z => (if (Function.update z j b) i = a then (1 : ℝ) else 0) /
          bernProb (w i) a * h (Function.update z j b)) w := mlExt_propensity _ w j b hb
    _ = mlExt (fun z => (if z i = a then (1 : ℝ) else 0) / bernProb (w i) a *
          h (Function.update z j b)) w := by simp only [Function.update_of_ne hji.symm]
    _ = mlExt (fun z => h (Function.update (Function.update z i a) j b)) w :=
      mlExt_propensity _ w i a ha
    _ = _ := by simp only [Function.update_comm hji.symm]

theorem bernProb_nonzero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (a : Bool) :
    bernProb p a ≠ 0 := by
  cases a <;> simp only [bernProb,Bool.false_eq_true,if_false,if_true]
  · linarith
  · exact ne_of_gt hp0

end Queelius.NetworkInterference

namespace DiffNeighbors.Bias
open Finset Queelius.NetworkInterference

theorem propensity_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → (ι → Bool) → ℝ) (i : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    bernExp p (condOutcome f i true) = bernExp p (fun z => ind (z i) / p * f i z) ∧
    bernExp p (condOutcome f i false) = bernExp p (fun z => (1 - ind (z i)) / (1 - p) * f i z) ∧
    ∀ (j : ι), j ≠ i → ∀ a b : Bool,
      bernExp p (fun z => condOutcome f i a (Function.update z j b)) =
        bernExp p (fun z => (if z i = a then (1 : ℝ) else 0) / bernProb p a *
          ((if z j = b then (1 : ℝ) else 0) / bernProb p b) * f i z) := by
  constructor
  · change mlExt (fun z => f i (Function.update z i true)) (fun _ => p) =
      mlExt (fun z => (if z i = true then 1 else 0) / p * f i z) (fun _ => p)
    exact (mlExt_propensity (f i) (fun _ => p) i true (bernProb_nonzero p hp0 hp1 true)).symm
  constructor
  · have h := (mlExt_propensity (f i) (fun _ => p) i false (bernProb_nonzero p hp0 hp1 false)).symm
    change bernExp p (condOutcome f i false) = _ at h
    rw [h]
    apply congrArg (fun g : (ι → Bool) → ℝ => mlExt g (fun _ => p))
    funext z
    cases hz : z i <;> simp [ind,bernProb,hz]
  · intro j hji a b
    exact (mlExt_two_propensity (f i) (fun _ => p) i j hji a b
      (bernProb_nonzero p hp0 hp1 a) (bernProb_nonzero p hp0 hp1 b)).symm

end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem mlExt_contDiff (h : (ι → Bool) → ℝ) : ContDiff ℝ ⊤ (mlExt h) := by
  unfold mlExt
  apply ContDiff.sum
  intro z hz
  apply ContDiff.mul _ contDiff_const
  apply contDiff_prod
  intro j hj
  split_ifs <;> fun_prop

theorem fderiv_coordinate (h : (ι → Bool) → ℝ) (w : ι → ℝ) (j : ι) :
    fderiv ℝ (mlExt h) w (Pi.single j 1) =
      mlExt (fun z => h (Function.update z j true)) w -
      mlExt (fun z => h (Function.update z j false)) w := by
  have hd := (mlExt_contDiff h).differentiable (by norm_num) w
  have hd' : HasFDerivAt (mlExt h) (fderiv ℝ (mlExt h) w) (Function.update w j (w j)) := by
    simpa using hd.hasFDerivAt
  have hc := hd'.comp_hasDerivAt (w j) (hasDerivAt_update w j (w j))
  exact hc.unique (first_partial h w j)

theorem diagonal_derivative (h : (ι → Bool) → ℝ) (p : ℝ) :
    HasDerivAt (fun t => mlExt h (fun _ => t))
      (∑ j, (mlExt (fun z => h (Function.update z j true)) (fun _ => p) -
        mlExt (fun z => h (Function.update z j false)) (fun _ => p))) p := by
  have hd := (mlExt_contDiff h).differentiable (by norm_num) (fun _ => p)
  have hc := hd.hasFDerivAt.comp_hasDerivAt p
    (hasDerivAt_pi.mpr (fun _ : ι => hasDerivAt_id p))
  have hone : (fun _ : ι => (1 : ℝ)) = ∑ j : ι, Pi.single j 1 := by
    ext k
    simp
  change HasDerivAt (fun t => mlExt h (fun _ => t))
    (fderiv ℝ (mlExt h) (fun _ => p) (fun _ => 1)) p at hc
  rw [hone,map_sum] at hc
  simpa only [fderiv_coordinate] using hc

theorem second_diagonal_derivative (h : (ι → Bool) → ℝ) (p : ℝ) :
    HasDerivAt (fun t => ∑ j, (mlExt (fun z => h (Function.update z j true)) (fun _ => t) -
      mlExt (fun z => h (Function.update z j false)) (fun _ => t)))
      (∑ j, ∑ k ∈ Finset.univ.erase j, mlExt (fun z => secondDiff h j k z) (fun _ => p)) p := by
  have hd := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
    (diagonal_derivative (fun z => h (Function.update z j true)) p).sub
      (diagonal_derivative (fun z => h (Function.update z j false)) p))
  convert hd using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_sub_distrib]
  have hdiag : (mlExt (fun z => h (Function.update (Function.update z j true) j true)) (fun _ => p) -
    mlExt (fun z => h (Function.update (Function.update z j false) j true)) (fun _ => p)) -
    (mlExt (fun z => h (Function.update (Function.update z j true) j false)) (fun _ => p) -
    mlExt (fun z => h (Function.update (Function.update z j false) j false)) (fun _ => p)) = 0 := by
    simp only [Function.update_idem,sub_self]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),hdiag,add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp only [secondDiff,mlExt_add,mlExt_sub,Function.update_comm hkj]
  ring

end Queelius.NetworkInterference

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def ipw (p : ℝ) (a : Bool) (z : ι → Bool) (i : ι) : ℝ :=
  (if z i = a then (1 : ℝ) else 0) / bernProb p a

theorem eta_ipw (p : ℝ) (z : ι → Bool) (i : ι) :
    eta p z i = ipw p true z i - ipw p false z i := by
  cases hz : z i <;> simp [eta,ipw,bernProb,ind,hz]

theorem xi_ipw (p : ℝ) (z : ι → Bool) (i : ι) :
    xi p z i = (1-p) * ipw p true z i + p * ipw p false z i := by
  cases hz : z i <;> simp [xi,ipw,bernProb,ind,hz,div_eq_mul_inv]

theorem bernExp_ipw (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h : (ι → Bool) → ℝ) (i : ι) (a : Bool) :
    bernExp p (fun z => ipw p a z i * h z) =
      bernExp p (fun z => h (Function.update z i a)) :=
  mlExt_propensity h (fun _ => p) i a (bernProb_nonzero p hp0 hp1 a)

theorem bernExp_two_ipw (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h : (ι → Bool) → ℝ) (i j : ι) (hji : j ≠ i) (a b : Bool) :
    bernExp p (fun z => ipw p a z i * ipw p b z j * h z) =
      bernExp p (fun z => h (Function.update (Function.update z j b) i a)) :=
  mlExt_two_propensity h (fun _ => p) i j hji a b
    (bernProb_nonzero p hp0 hp1 a) (bernProb_nonzero p hp0 hp1 b)

theorem bernExp_eta (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h : (ι → Bool) → ℝ) (i : ι) :
    bernExp p (fun z => eta p z i * h z) =
      bernExp p (fun z => h (Function.update z i true)) -
      bernExp p (fun z => h (Function.update z i false)) := by
  simp_rw [eta_ipw,sub_mul]
  change mlExt _ _ = _
  rw [mlExt_sub]
  exact congrArg₂ (· - ·) (bernExp_ipw p hp0 hp1 h i true) (bernExp_ipw p hp0 hp1 h i false)

theorem bernExp_xi_eta (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (h : (ι → Bool) → ℝ) (i j : ι) (hji : j ≠ i) :
    bernExp p (fun z => xi p z i * eta p z j * h z) =
      (1-p) * (bernExp p (fun z => h (Function.update (Function.update z j true) i true)) -
        bernExp p (fun z => h (Function.update (Function.update z j false) i true))) +
      p * (bernExp p (fun z => h (Function.update (Function.update z j true) i false)) -
        bernExp p (fun z => h (Function.update (Function.update z j false) i false))) := by
  have heq (z : ι → Bool) : xi p z i * eta p z j * h z =
      (1-p) * (ipw p true z i * ipw p true z j * h z - ipw p true z i * ipw p false z j * h z) +
      p * (ipw p false z i * ipw p true z j * h z - ipw p false z i * ipw p false z j * h z) := by
    rw [xi_ipw,eta_ipw]; ring
  simp_rw [heq]
  simp only [bernExp,mlExt_add,mlExt_smul,mlExt_sub]
  change (1-p) * (bernExp p _ - bernExp p _) + p * (bernExp p _ - bernExp p _) = _
  simp only [bernExp_two_ipw p hp0 hp1 h i j hji]
  rfl

end Queelius.NetworkInterference

namespace DiffNeighbors.Bias
open Finset Queelius.NetworkInterference

theorem dn_unbiased_first_order {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (f : ι → (ι → Bool) → ℝ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    bernExp p (dnEstimator G p f) = (Fintype.card ι : ℝ)⁻¹ * ∑ i,
      (bernExp p (condOutcome f i true)
        + ∑ j ∈ G.neighborFinset i, (1 - p) *
            (bernExp p (fun z => condOutcome f i true (Function.update z j true))
              - bernExp p (fun z => condOutcome f i true (Function.update z j false)))
        - bernExp p (condOutcome f i false)
        - ∑ j ∈ G.neighborFinset i, (0 - p) *
            (bernExp p (fun z => condOutcome f i false (Function.update z j true))
              - bernExp p (fun z => condOutcome f i false (Function.update z j false)))) := by
  have heq (z : ι → Bool) : dnEstimator G p f z = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (eta p z i * f i z + ∑ j ∈ G.neighborFinset i, xi p z i * eta p z j * f i z) := by
    rw [credit_assignment]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [add_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  change bernExp p (fun z => dnEstimator G p f z) = _
  simp_rw [heq]
  unfold bernExp
  rw [mlExt_smul,mlExt_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mlExt_add,mlExt_sum]
  change bernExp p (fun z => eta p z i * f i z) +
    (∑ j ∈ G.neighborFinset i, bernExp p (fun z => xi p z i * eta p z j * f i z)) = _
  rw [bernExp_eta p hp0 hp1]
  have hsum : (∑ j ∈ G.neighborFinset i, bernExp p (fun z => xi p z i * eta p z j * f i z)) =
      ∑ j ∈ G.neighborFinset i,
        ((1-p) * (bernExp p (fun z => f i (Function.update (Function.update z j true) i true)) -
          bernExp p (fun z => f i (Function.update (Function.update z j false) i true))) +
         p * (bernExp p (fun z => f i (Function.update (Function.update z j true) i false)) -
          bernExp p (fun z => f i (Function.update (Function.update z j false) i false)))) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact bernExp_xi_eta p hp0 hp1 (f i) i j ((G.mem_neighborFinset i j).mp hj).ne.symm
  rw [hsum,Finset.sum_add_distrib]
  unfold condOutcome
  simp only [bernExp,zero_sub,neg_mul,Finset.sum_neg_distrib]
  ring

end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset Set
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem diagonal_taylor (h : (ι → Bool) → ℝ) (p q : ℝ) :
    ∃ s ∈ Set.uIcc p q,
      mlExt h (fun _ => q) - mlExt h (fun _ => p) -
        ∑ j, (q-p) * (mlExt (fun z => h (Function.update z j true)) (fun _ => p) -
          mlExt (fun z => h (Function.update z j false)) (fun _ => p)) =
      (1/2) * ∑ j, ∑ k ∈ Finset.univ.erase j,
        (q-p)^2 * mlExt (fun z => secondDiff h j k z) (fun _ => s) := by
  by_cases hpq : p=q
  · subst q
    exact ⟨p,by simp,by simp⟩
  let g : ℝ → ℝ := fun t => mlExt h (fun _ => t)
  have hg : ContDiff ℝ ⊤ g := (mlExt_contDiff h).comp (by fun_prop)
  have hd : deriv g = fun t => ∑ j, (mlExt (fun z => h (Function.update z j true)) (fun _ => t) -
      mlExt (fun z => h (Function.update z j false)) (fun _ => t)) := by
    funext t
    exact (diagonal_derivative h t).deriv
  have hdd (t : ℝ) : iteratedDeriv 2 g t =
      ∑ j, ∑ k ∈ Finset.univ.erase j, mlExt (fun z => secondDiff h j k z) (fun _ => t) := by
    rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,hd]
    exact (second_diagonal_derivative h t).deriv
  obtain ⟨s,hs,ht⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=1) hpq
    (hg.of_le (by norm_num)).contDiffOn
  have hw : derivWithin g (uIcc p q) p =
      ∑ j, (mlExt (fun z => h (Function.update z j true)) (fun _ => p) -
        mlExt (fun z => h (Function.update z j false)) (fun _ => p)) :=
    (diagonal_derivative h p).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_uIcc hpq) p (by simp))
  refine ⟨s,⟨le_of_lt hs.1,le_of_lt hs.2⟩,?_⟩
  simp only [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_one] at ht
  norm_num only [hw,hdd,Nat.factorial,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,zero_add,mul_one,one_mul,inv_one,pow_one,smul_eq_mul] at ht
  rw [iteratedDerivWithin_one,hw] at ht
  dsimp [g] at ht
  simp only [← Finset.mul_sum]
  nlinarith [ht]

end Queelius.NetworkInterference

namespace DiffNeighbors.Bias
open Finset

theorem taylor_remainder {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → Bool) → ℝ) (a : Bool)
    (p : ℝ) :
    ∃ s ∈ Set.uIcc p (ind a),
      mlExt h (fun _ => ind a) - mlExt h (fun _ => p)
        - ∑ j, (ind a - p) * (mlExt (fun z => h (Function.update z j true)) (fun _ => p)
            - mlExt (fun z => h (Function.update z j false)) (fun _ => p))
      = (1 / 2) * ∑ j, ∑ k ∈ Finset.univ.erase j,
          (ind a - p) ^ 2 * mlExt (fun z => secondDiff h j k z) (fun _ => s) :=
  Queelius.NetworkInterference.diagonal_taylor h p (ind a)

end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem mlExt_ind (w : ι → ℝ) (i : ι) : mlExt (fun z => ind (z i)) w = w i := by
  have h := mlExt_indicator (fun _ : ι → Bool => (1 : ℝ)) w i true
  simpa only [bernProb,if_true,mul_one,mlExt_const,ind] using h

theorem mlExt_pair_ind (w : ι → ℝ) (i j : ι) (hji : j ≠ i) :
    mlExt (fun z => ind (z i) * ind (z j)) w = w i * w j := by
  have h := mlExt_indicator (fun z => ind (z j)) w i true
  simp only [bernProb,if_true,Function.update_of_ne hji] at h
  change mlExt (fun z => ind (z i) * ind (z j)) w = w i * mlExt (fun z => ind (z j)) w at h
  rw [h,mlExt_ind]

end Queelius.NetworkInterference

namespace Queelius.NetworkInterference.Controls
open DiffNeighbors.Bias Finset

def binaryPair (z : Fin 2 → Bool) : ℝ := ind (z 0) * ind (z 1)

theorem pair_polynomial (w : Fin 2 → ℝ) : mlExt binaryPair w = w 0 * w 1 :=
  mlExt_pair_ind w 0 1 (by decide)

theorem raw_pair_third : bernExp (1/3) binaryPair = 1/9 := by
  rw [bernExp,pair_polynomial]
  norm_num

theorem weighted_pair_third :
    bernExp (1/3) (fun z => ipw (1/3) true z 0 * ipw (1/3) true z 1 * binaryPair z) = 1 := by
  rw [bernExp_two_ipw (1/3) (by norm_num) (by norm_num) binaryPair 0 1 (by decide)]
  simp [binaryPair,ind,bernExp,mlExt_const]

theorem cross_second_nonzero :
    mlExt (fun z => secondDiff binaryPair 0 1 z) (fun _ => (1/3 : ℝ)) = 1 := by
  have hd : (fun z => secondDiff binaryPair 0 1 z) = (fun _ => (1 : ℝ)) := by
    funext z
    norm_num [secondDiff,binaryPair,ind,Function.update_apply,Fin.ext_iff]
  rw [hd,mlExt_const]

theorem endpoint_inverse_probability_fails :
    bernExp (0 : ℝ) (fun z : Fin 1 → Bool => ipw 0 true z 0 * ind (z 0)) = 0 ∧
    bernExp (0 : ℝ) (fun z : Fin 1 → Bool => ind ((Function.update z 0 true) 0)) = 1 := by
  constructor <;> simp [ipw,bernProb,ind,bernExp,mlExt_const]

end Queelius.NetworkInterference.Controls

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem cond_update_outside (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (i : ι) (a : Bool) (j : ι) (hj : j ∉ G.neighborFinset i) (z : ι → Bool) (b : Bool) :
    condOutcome f i a (Function.update z j b) = condOutcome f i a z := by
  unfold condOutcome
  apply hf i
  intro k hk
  by_cases hki : k=i
  · subst k; simp
  · have hkj : k ≠ j := by
      rintro rfl
      exact hj ((G.mem_neighborFinset i k).mpr (hk.resolve_left hki))
    simp [Function.update_of_ne hki,Function.update_of_ne hkj]

theorem first_difference_outside (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (i : ι) (a : Bool) (j : ι) (hj : j ∉ G.neighborFinset i) (w : ι → ℝ) :
    mlExt (fun z => condOutcome f i a (Function.update z j true)) w -
      mlExt (fun z => condOutcome f i a (Function.update z j false)) w = 0 := by
  simp only [cond_update_outside G f hf i a j hj,sub_self]

theorem second_difference_outside (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (i : ι) (a : Bool) (j k : ι) (hjk : j ∉ G.neighborFinset i ∨ k ∉ G.neighborFinset i)
    (z : ι → Bool) : secondDiff (condOutcome f i a) j k z = 0 := by
  by_cases heq : j=k
  · subst k; simp [secondDiff,Function.update_idem]
  rcases hjk with hj|hk
  · simp only [secondDiff,Function.update_comm heq,cond_update_outside G f hf i a j hj]
    ring
  · simp only [secondDiff,cond_update_outside G f hf i a k hk]
    ring

theorem sum_restrict (S : Finset ι) (F : ι → ℝ) (hF : ∀ j, j ∉ S → F j=0) :
    ∑ j, F j = ∑ j ∈ S, F j := by
  symm
  exact Finset.sum_subset (Finset.subset_univ S) (fun j hj hnot => hF j hnot)

theorem offdiag_sum_restrict (S : Finset ι) (F : ι → ι → ℝ)
    (hF : ∀ j k, j ∉ S ∨ k ∉ S → F j k=0) :
    (∑ j, ∑ k ∈ Finset.univ.erase j, F j k) = ∑ j ∈ S, ∑ k ∈ S.erase j, F j k := by
  rw [sum_restrict S _ (by intro j hj; apply Finset.sum_eq_zero; intro k hk; exact hF j k (Or.inl hj))]
  apply Finset.sum_congr rfl
  intro j hj
  symm
  apply Finset.sum_subset (Finset.erase_subset_erase j (Finset.subset_univ S))
  intro k hk hnot
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  apply hF j k
  right
  intro hks
  exact hnot (Finset.mem_erase.mpr ⟨hkj,hks⟩)

theorem endpoint_extension (h : (ι → Bool) → ℝ) (a : Bool) :
    mlExt h (fun _ => ind a) = h (fun _ => a) := by
  unfold mlExt
  have hw (z : ι → Bool) : (∏ j, if z j then ind a else 1-ind a) =
      if z=(fun _ => a) then 1 else 0 := by
    by_cases hz : z=(fun _ => a)
    · subst z; cases a <;> simp [ind]
    · rw [if_neg hz]
      obtain ⟨j,hj⟩ := Function.ne_iff.mp hz
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      cases a <;> cases hzj : z j <;> simp_all [ind]
  simp only [hw,ite_mul,one_mul,zero_mul]
  simp

end Queelius.NetworkInterference

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset Set
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def firstApprox (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (i : ι) (a : Bool) (p : ℝ) : ℝ :=
  bernExp p (condOutcome f i a) + ∑ j ∈ G.neighborFinset i, (ind a-p) *
    (bernExp p (fun z => condOutcome f i a (Function.update z j true)) -
      bernExp p (fun z => condOutcome f i a (Function.update z j false)))

theorem conditional_error_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (i : ι) (a : Bool) (p ε : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hε : IsSmooth ε (condOutcome f i a)) :
    |f i (fun _ => a) - firstApprox G f i a p| ≤ (1/2) * ((G.maxDegree : ℝ)^2*ε) := by
  obtain ⟨s,hs,ht⟩ := taylor_remainder (condOutcome f i a) a p
  have hgrad := sum_restrict (G.neighborFinset i)
    (fun j => (ind a-p) * (mlExt (fun z => condOutcome f i a (Function.update z j true)) (fun _ => p) -
      mlExt (fun z => condOutcome f i a (Function.update z j false)) (fun _ => p))) (by
    intro j hj; rw [first_difference_outside G f hf i a j hj,mul_zero])
  have hhess := offdiag_sum_restrict (G.neighborFinset i)
    (fun j k => (ind a-p)^2 * mlExt (fun z => secondDiff (condOutcome f i a) j k z) (fun _ => s)) (by
      intro j k hjk
      simp only [second_difference_outside G f hf i a j k hjk,mlExt_const,mul_zero])
  rw [endpoint_extension,hgrad,hhess] at ht
  have hend : condOutcome f i a (fun _ => a) = f i (fun _ => a) := by simp [condOutcome]
  rw [hend] at ht
  have hs01 : s ∈ Set.Icc (0:ℝ) 1 := by
    have ha : ind a ∈ Set.Icc (0:ℝ) 1 := by cases a <;> norm_num [ind]
    rcases Set.mem_uIcc.mp hs with hs|hs
    · exact ⟨hp.1.trans hs.1,hs.2.trans ha.2⟩
    · exact ⟨ha.1.trans hs.1,hs.2.trans hp.2⟩
  have he : f i (fun _ => a) - firstApprox G f i a p = (1/2) *
      ∑ j ∈ G.neighborFinset i, ∑ k ∈ (G.neighborFinset i).erase j,
        (ind a-p)^2 * mlExt (fun z => secondDiff (condOutcome f i a) j k z) (fun _ => s) := by
    unfold firstApprox bernExp
    linarith [ht]
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  exact mul_le_mul_of_nonneg_left (remainder_bound G f i a ε p (fun _ => s) hp (fun _ => hs01) hε)
    (by norm_num)

end Queelius.NetworkInterference

end

section
noncomputable section
namespace Queelius.NetworkInterference
open DiffNeighbors.Bias Finset
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem expected_firstApprox (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (p : ℝ) (hp0 : 0<p) (hp1 : p<1) :
    bernExp p (dnEstimator G p f) = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (firstApprox G f i true p - firstApprox G f i false p) := by
  rw [dn_unbiased_first_order G f p hp0 hp1]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  unfold firstApprox
  simp only [ind,if_true,Bool.false_eq_true,if_false]
  ring

theorem unit_bias_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (i : ι) (p ε : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1)
    (hε : ∀ a, IsSmooth ε (condOutcome f i a)) :
    |(f i (fun _ => true) - f i (fun _ => false)) -
      (firstApprox G f i true p - firstApprox G f i false p)| ≤ (G.maxDegree : ℝ)^2*ε := by
  have h1 := conditional_error_bound G f hf i true p ε hp (hε true)
  have h0 := conditional_error_bound G f hf i false p ε hp (hε false)
  have he : (f i (fun _ => true) - f i (fun _ => false)) -
      (firstApprox G f i true p - firstApprox G f i false p) =
      (f i (fun _ => true)-firstApprox G f i true p) -
      (f i (fun _ => false)-firstApprox G f i false p) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

end Queelius.NetworkInterference

namespace DiffNeighbors.Bias
open Finset Queelius.NetworkInterference

theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (p ε : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hε : ∀ i, ∀ a : Bool, IsSmooth ε (condOutcome f i a)) :
    |ate f - bernExp p (dnEstimator G p f)| ≤ (G.maxDegree : ℝ) ^ 2 * ε := by
  cases isEmpty_or_nonempty ι with
  | inl he =>
    simp [ate,bernExp,dnEstimator,mlExt,SimpleGraph.maxDegree]
  | inr hn =>
    have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [expected_firstApprox G f p hp0 hp1,ate,← mul_sub,← Finset.sum_sub_distrib,
      abs_mul,abs_of_nonneg (inv_nonneg.mpr (le_of_lt hc))]
    calc
      _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i,
          |(f i (fun _ => true)-f i (fun _ => false)) -
            (firstApprox G f i true p-firstApprox G f i false p)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (le_of_lt hc))
      _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _ : ι, (G.maxDegree : ℝ)^2*ε :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
          unit_bias_bound G f hf i p ε ⟨le_of_lt hp0,le_of_lt hp1⟩ (hε i)))
          (inv_nonneg.mpr (le_of_lt hc))
      _ = (G.maxDegree : ℝ)^2*ε := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        rw [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hc),one_mul]

end DiffNeighbors.Bias

end

section
noncomputable section
namespace Queelius.NetworkInterference.Controls
open DiffNeighbors.Bias Finset

theorem pair_taylor_half_factor :
    mlExt binaryPair (fun _ => 1) - mlExt binaryPair (fun _ => 0) -
      ∑ j : Fin 2, (1-0) * (mlExt (fun z => binaryPair (Function.update z j true)) (fun _ => 0) -
        mlExt (fun z => binaryPair (Function.update z j false)) (fun _ => 0)) = 1 := by
  rw [pair_polynomial,pair_polynomial]
  norm_num [binaryPair,Fin.sum_univ_two,mlExt_ind,mlExt_const,ind]
  change mlExt (fun z : Fin 2 → Bool => ind (z 1)) (fun _ => 0) +
    mlExt (fun z : Fin 2 → Bool => ind (z 0)) (fun _ => 0) = 0
  rw [mlExt_ind,mlExt_ind]
  norm_num

theorem pair_hessian_double :
    (∑ j : Fin 2, ∑ k ∈ Finset.univ.erase j,
      mlExt (fun z => secondDiff binaryPair j k z) (fun _ => (1/3:ℝ))) = 2 := by
  have hs (j k : Fin 2) : (fun z => secondDiff binaryPair j k z) = fun _ => if j=k then 0 else 1 := by
    fin_cases j <;> fin_cases k <;> funext z <;>
      norm_num [secondDiff,binaryPair,ind,Function.update_apply,Fin.ext_iff]
  simp only [hs,mlExt_const]
  norm_num [Fin.sum_univ_two,Finset.sum_erase_eq_sub]

def cubicOutcome (i : Fin 3) (z : Fin 3 → Bool) : ℝ :=
  if i=2 then ind (z 2) * (ind (z 0)*ind (z 1)) else 0

theorem cubic_interference : NeighborhoodInterference (⊤ : SimpleGraph (Fin 3)) cubicOutcome := by
  intro i z z' h
  have hz : z=z' := by
    funext j
    apply h j
    by_cases hj : j=i
    · exact Or.inl hj
    · exact Or.inr (by simpa using Ne.symm hj)
  rw [hz]

theorem cubic_smooth (i : Fin 3) (a : Bool) : IsSmooth 1 (condOutcome cubicOutcome i a) := by
  by_cases hi : i=2
  · subst i
    cases a
    · intro z j k
      norm_num [secondDiff,condOutcome,cubicOutcome,ind]
    · have he : condOutcome cubicOutcome 2 true = condOutcome pairOutcome 2 true := by
        funext z
        norm_num [condOutcome,cubicOutcome,pairOutcome,ind]
      rw [he]
      exact pair_smooth
  · intro z j k
    norm_num [secondDiff,condOutcome,cubicOutcome,hi]

theorem cubic_conditional (i : Fin 3) (a : Bool) :
    condOutcome cubicOutcome i a =
      if i=2 ∧ a=true then (fun z => ind (z 0)*ind (z 1)) else (fun _ => 0) := by
  fin_cases i <;> cases a <;> funext z <;>
    norm_num [condOutcome,cubicOutcome,ind,Function.update_apply,Fin.ext_iff]

theorem cubic_firstApprox (i : Fin 3) (a : Bool) (p : ℝ) :
    firstApprox (⊤ : SimpleGraph (Fin 3)) cubicOutcome i a p =
      if i=2 ∧ a=true then p*p+2*(1-p)*p else 0 := by
  have hN : (⊤ : SimpleGraph (Fin 3)).neighborFinset 2 = {0,1} := by decide
  simp only [firstApprox,cubic_conditional,bernExp]
  by_cases h : i=2 ∧ a=true
  · obtain ⟨rfl,rfl⟩ := h
    simp only [and_self,ite_true,hN]
    norm_num only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_singleton,
      show (0 : Fin 3) ≠ 1 by decide,not_false_eq_true,Function.update_self,
      Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
      Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      show ind true=1 from rfl,show ind false=0 from rfl,mul_one,one_mul,mul_zero,zero_mul,
      mlExt_const,mlExt_ind,mlExt_pair_ind (ι:=Fin 3) _ 0 1 (by decide)]
    ring
  · simp only [h,ite_false,mlExt_const,sub_self,mul_zero,Finset.sum_const_zero,add_zero]

theorem cubic_expected_quarter :
    bernExp (1/2) (dnEstimator (⊤ : SimpleGraph (Fin 3)) (1/2) cubicOutcome) = 1/4 := by
  rw [expected_firstApprox _ _ (1/2) (by norm_num) (by norm_num)]
  simp only [cubic_firstApprox]
  norm_num [Fin.sum_univ_succ]

theorem cubic_nonzero_bias :
    |ate cubicOutcome - bernExp (1/2) (dnEstimator (⊤ : SimpleGraph (Fin 3)) (1/2) cubicOutcome)| = 1/12 := by
  rw [cubic_expected_quarter]
  norm_num [ate,cubicOutcome,ind,Fin.sum_univ_succ]

theorem cubic_bound_checked :
    |ate cubicOutcome - bernExp (1/2) (dnEstimator (⊤ : SimpleGraph (Fin 3)) (1/2) cubicOutcome)| ≤
      ((⊤ : SimpleGraph (Fin 3)).maxDegree : ℝ)^2 * 1 :=
  theorem_1 _ cubicOutcome cubic_interference (1/2) 1 (by norm_num) (by norm_num) cubic_smooth

end Queelius.NetworkInterference.Controls

end

universe audit_u0

theorem solution : (
  ∀ {ι : Type audit_u0} [inst : Fintype ι] [inst_1 : DecidableEq ι] (h : (ι → Bool) → Real) (a : Bool) (p : Real),
    @Exists Real fun (s : Real) =>
      And
        (@Membership.mem Real (Set Real) (@Set.instMembership Real)
          (@Set.uIcc Real Real.lattice p (DiffNeighbors.Bias.ind a)) s)
        (@Eq Real
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
            (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
              (@DiffNeighbors.Bias.mlExt ι inst inst_1 h fun (x : ι) => DiffNeighbors.Bias.ind a)
              (@DiffNeighbors.Bias.mlExt ι inst inst_1 h fun (x : ι) => p))
            (@Finset.sum ι Real Real.instAddCommMonoid (@Finset.univ ι inst) fun (j : ι) =>
              @HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (DiffNeighbors.Bias.ind a) p)
                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                  (@DiffNeighbors.Bias.mlExt ι inst inst_1
                    (fun (z : ι → Bool) => h (@Function.update ι (fun (a : ι) => Bool) inst_1 z j Bool.true))
                    fun (x : ι) => p)
                  (@DiffNeighbors.Bias.mlExt ι inst inst_1
                    (fun (z : ι → Bool) => h (@Function.update ι (fun (a : ι) => Bool) inst_1 z j Bool.false))
                    fun (x : ι) => p))))
          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
              (@OfNat.ofNat Real (nat_lit 2)
                (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@Finset.sum ι Real Real.instAddCommMonoid (@Finset.univ ι inst) fun (j : ι) =>
              @Finset.sum ι Real Real.instAddCommMonoid (@Finset.erase ι inst_1 (@Finset.univ ι inst) j) fun (k : ι) =>
                @HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (DiffNeighbors.Bias.ind a) p)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DiffNeighbors.Bias.mlExt ι inst inst_1
                    (fun (z : ι → Bool) => @DiffNeighbors.Bias.secondDiff ι inst_1 h j k z) fun (x : ι) => s))))
) := @DiffNeighbors.Bias.taylor_remainder
