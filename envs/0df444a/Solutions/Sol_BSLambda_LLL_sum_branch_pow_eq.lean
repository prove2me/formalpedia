-- Prove2me | solution 1 for BSLambda.LLL.sum_branch_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:11.078484+00:00
-- url     : https://prove2.me/submissions/92fa13d8-84f6-4305-9646-7855cf6f0d10

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_mem_ownerGates
public import Theorems.Thm_BSLambda_LLL_mem_arcSet
public import Theorems.Thm_BSLambda_LLL_mem_missSet
public import Theorems.Thm_BSLambda_LLL_missSet_subset_missSet
public import Theorems.Thm_BSLambda_LLL_mem_zeroSet
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_nonOwners
public import Theorems.Thm_BSLambda_LLL_Flag1_mem_supp
public import Theorems.Thm_BSLambda_LLL_mem_missArcs
public import Theorems.Thm_BSLambda_LLL_mem_discSet
public import Theorems.Thm_BSLambda_Construction_card_block
public import Theorems.Thm_BSLambda_Construction_gateCoord_fst
public import Theorems.Thm_BSLambda_Construction_ind_eq_false_iff
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_iff
public import Theorems.Thm_BSLambda_Construction_mem_block
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_mem_fibre
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_univ
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_ne
public import Theorems.Thm_BSLambda_PartialAssign_dist_eq_zero_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_false_iff
public import Theorems.Thm_BSLambda_PartialAssign_indUnion_eq_true_iff
public import Theorems.Thm_BSLambda_PartialAssign_mem_cube
public import Theorems.Thm_BSLambda_PartialAssign_mem_fixedSet
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet
public import Theorems.Thm_BSLambda_PartialAssign_proj_apply
public import Theorems.Thm_BSLambda_PartialAssign_proj_sat
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_middles
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.Construction.card_block
attribute [local simp] BSLambda.Construction.gateCoord_fst
attribute [local simp] BSLambda.Construction.ind_eq_false_iff
attribute [local simp] BSLambda.Construction.ind_eq_true_iff
attribute [local simp] BSLambda.Construction.mem_block
attribute [local simp] BSLambda.LLL.avoid_empty
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.mem_fibre
attribute [local simp] BSLambda.LLL.mem_nbr
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ
attribute [local simp] BSLambda.PartialAssign.dist_eq_zero_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_false_iff
attribute [local simp] BSLambda.PartialAssign.indUnion_eq_true_iff
attribute [local simp] BSLambda.PartialAssign.mem_cube
attribute [local simp] BSLambda.PartialAssign.mem_fixedSet
attribute [local simp] BSLambda.PartialAssign.mem_violSet
attribute [local simp] BSLambda.PartialAssign.proj_apply
attribute [local simp] BSLambda.PartialAssign.proj_sat
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_middles
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.zeroInput_apply


attribute [local simp] BSLambda.LLL.mem_ownerGates
attribute [local simp] BSLambda.LLL.mem_arcSet
attribute [local simp] BSLambda.LLL.mem_missSet
attribute [local gcongr] BSLambda.LLL.missSet_subset_missSet
attribute [local simp] BSLambda.LLL.mem_zeroSet
attribute [local simp] BSLambda.LLL.Flag1.mem_nonOwners
attribute [local simp] BSLambda.LLL.Flag1.mem_supp
attribute [local simp] BSLambda.LLL.mem_missArcs
attribute [local simp] BSLambda.LLL.mem_discSet
section
@[expose] public section
namespace BSLambda
namespace LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
section ArcSet
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
variable (hT : IsTournament Arc)
include hT
end ArcSet
section MissSet
omit [Fintype ι] [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ γ' : ι → ι → Fin r} {Z : ι → Finset (Fin r)}
  {T T' S : Finset ι} {i j : ι}
end MissSet
namespace Flag1
section Membership
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}
namespace Active
variable (hF : F.Active Arc)
include hF
end Active
end Membership
end Flag1
section MissArcs
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
end MissArcs
omit [Fintype ι] in
/-- The two innermost sums of `sum_branch_pow_eq` are constant: there are `r ^ |L|` choices of
discretionary zeros and `C(28, 8 - |L|)` choices of the exceptional arc set. -/
private theorem sum_pi_sum_powersetCard_const {AA : Finset (ι × ι)} (hAA : AA.card = 28)
    {L : Finset ι} (hL : L.card ≤ 8) :
    (∑ _w ∈ (L.pi fun _ ↦ (Finset.univ : Finset (Fin r))),
        ∑ _X ∈ AA.powersetCard (8 - L.card), ((2 : ℝ) / r) ^ (AA.card - (8 - L.card)))
      = (r : ℝ) ^ L.card * (Nat.choose 28 (8 - L.card) : ℝ) * ((2 : ℝ) / r) ^ (20 + L.card) := by
  have hexp : AA.card - (8 - L.card) = 20 + L.card := by omega
  rw [hexp, Finset.sum_const, Finset.sum_const, Finset.card_powersetCard, hAA, Finset.card_pi]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul]
  push_cast
  ring
private theorem pow_mul_div_pow_add (hr : (r : ℝ) ≠ 0) (c : ℝ) (n l : ℕ) :
    (r : ℝ) ^ l * c * ((2 : ℝ) / r) ^ (n + l) = c * 2 ^ n * 2 ^ l / (r : ℝ) ^ n := by
  rw [div_pow, pow_add, pow_add]
  field_simp
end LLL
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] {S : Finset ι} {h : ι} (hh : h ∈ S) (hS : S.card = 9)
    {AA : Finset (ι × ι)} (hAA : AA.card = 28) :
    ∑ L ∈ (S.erase h).powerset, ∑ _w ∈ (L.pi fun _ => (Finset.univ : Finset (Fin r))),
        ∑ _X ∈ AA.powersetCard (8 - L.card), ((2 : ℝ) / r) ^ (AA.card - (8 - L.card))
      = (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 := by
  classical
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hcard8 : (S.erase h).card = 8 := by rw [Finset.card_erase_of_mem hh, hS]
  rw [radiusTwoOwnerConst]
  rw [Finset.sum_congr rfl fun L hL ↦ sum_pi_sum_powersetCard_const hAA
      ((Finset.card_le_card (Finset.mem_powerset.mp hL)).trans hcard8.le),
    Finset.sum_powerset, hcard8]
  have step2 : ∀ l ∈ Finset.range 9,
      (∑ _L ∈ (S.erase h).powersetCard l,
        (r : ℝ) ^ l * (Nat.choose 28 (8 - l) : ℝ) * ((2 : ℝ) / r) ^ (20 + l))
      = (Nat.choose 8 l : ℝ) * (Nat.choose 28 (8 - l) : ℝ) * 2 ^ 20 * 2 ^ l / (r : ℝ) ^ 20 := by
    intro l _
    rw [Finset.sum_const, Finset.card_powersetCard, hcard8, nsmul_eq_mul,
      pow_mul_div_pow_add hr]
    ring
  calc
    (∑ j ∈ Finset.range (8 + 1), ∑ L ∈ (S.erase h).powersetCard j,
        (r : ℝ) ^ L.card * (Nat.choose 28 (8 - L.card) : ℝ) * ((2 : ℝ) / r) ^ (20 + L.card))
        = ∑ l ∈ Finset.range 9, ∑ _L ∈ (S.erase h).powersetCard l,
            (r : ℝ) ^ l * (Nat.choose 28 (8 - l) : ℝ) * ((2 : ℝ) / r) ^ (20 + l) := by
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun L hL ↦ ?_
          rw [(Finset.mem_powersetCard.mp hL).2]
    _ = ∑ l ∈ Finset.range 9,
          (Nat.choose 8 l : ℝ) * (Nat.choose 28 (8 - l) : ℝ) * 2 ^ 20 * 2 ^ l / (r : ℝ) ^ 20 :=
          Finset.sum_congr rfl step2
    _ = ((2 ^ 20 * ∑ l ∈ Finset.range 9,
          Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l : ℕ) : ℝ) / (r : ℝ) ^ 20 := by
          rw [eq_div_iff (pow_ne_zero 20 hr), Finset.sum_mul]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          field_simp
          ring
end BSLambda.LLL
