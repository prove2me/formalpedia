-- Prove2me | solution 1 for BSLambda.exists_neg_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:45.405037+00:00
-- url     : https://prove2.me/submissions/c618d255-f503-41ed-9487-eb6b5d5cad40

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply


section
@[expose] public section
namespace BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
/-- The sign pattern takes the values `±1`, so it never vanishes. -/
private theorem signPattern_ne_zero (f : Input V → Bool) (x : Input V) : signPattern f x ≠ 0 := by
  rw [signPattern]
  split <;> norm_num
omit [DecidableEq V] in
/-- The sign pattern flips across every edge of the sensitivity graph, so scaling coordinate `y`
by `signPattern f y` is the same as scaling the whole `x`-row by `-signPattern f x`. -/
private theorem adj_mul_signPattern (f : Input V → Bool) (v : Input V → ℝ) (x y : Input V) :
    adj f x y * (signPattern f y * v y) = -signPattern f x * (adj f x y * v y) := by
  by_cases h : hammingDist x y = 1 ∧ f x ≠ f y
  · have hfy : f y = !f x := by
      revert h
      cases f x <;> cases f y <;> simp
    rw [adj_apply, if_pos h, signPattern, signPattern, hfy]
    cases f x <;> simp
  · rw [adj_apply, if_neg h]
    ring
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) {μ : ℝ} {v : Input V → ℝ} (hv : v ≠ 0)
    (hev : adj f *ᵥ v = μ • v) : ∃ w : Input V → ℝ, w ≠ 0 ∧ adj f *ᵥ w = (-μ) • w := by
  refine ⟨fun x ↦ signPattern f x * v x, ?_, ?_⟩
  · intro hw
    refine hv (funext fun x ↦ ?_)
    exact (mul_eq_zero.1 (congrFun hw x)).resolve_left (signPattern_ne_zero f x)
  · funext x
    have hvx : ∑ y : Input V, adj f x y * v y = μ * v x := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hev x
    calc (adj f *ᵥ fun y ↦ signPattern f y * v y) x
        = ∑ y : Input V, adj f x y * (signPattern f y * v y) := rfl
      _ = ∑ y : Input V, -signPattern f x * (adj f x y * v y) :=
          Finset.sum_congr rfl fun y _ ↦ adj_mul_signPattern f v x y
      _ = -signPattern f x * ∑ y : Input V, adj f x y * v y := (Finset.mul_sum _ _ _).symm
      _ = -signPattern f x * (μ * v x) := by rw [hvx]
      _ = ((-μ) • fun y ↦ signPattern f y * v y) x := by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
end BSLambda
