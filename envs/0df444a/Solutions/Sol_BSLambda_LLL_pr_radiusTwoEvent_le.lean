-- Prove2me | solution 1 for BSLambda.LLL.pr_radiusTwoEvent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:43.690609+00:00
-- url     : https://prove2.me/submissions/77d223c5-dde5-4ce0-9678-738f453a7d91

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_radiusTwoConst_eq_nine_mul
public import Theorems.Thm_BSLambda_LLL_radiusTwoEvent_subset_biUnion_owner
public import Theorems.Thm_BSLambda_LLL_pr_intObstruction_owner_le
public import Theorems.Thm_BSLambda_LLL_pr_le_of_subset_biUnion


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
open scoped Classical
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) :
    pr (β := fun _ : ι × ι => Fin r) (radiusTwoEvent Arc S)
      ≤ (radiusTwoConst : ℝ) / (r : ℝ) ^ 20 := by
  have hb := pr_le_of_subset_biUnion (β := fun _ : ι × ι ↦ Fin r) S
    (fun h ↦ Finset.univ.filter fun ω : GateCfg ι r ↦ IntObstruction Arc 2 S h (toGamma ω))
    (radiusTwoEvent_subset_biUnion_owner Arc S)
  have hterm : ∀ h ∈ S, pr (β := fun _ : ι × ι ↦ Fin r)
      (Finset.univ.filter fun ω : GateCfg ι r ↦ IntObstruction Arc 2 S h (toGamma ω))
      ≤ (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 :=
    fun h hh ↦ pr_intObstruction_owner_le hT hS hh
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, hS, nsmul_eq_mul] at hsum
  rw [radiusTwoConst_eq_nine_mul]
  calc pr (β := fun _ : ι × ι ↦ Fin r) (radiusTwoEvent Arc S) ≤ _ := hb
    _ ≤ (9 : ℝ) * ((radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20) := by exact_mod_cast hsum
    _ = ((9 * radiusTwoOwnerConst : ℕ) : ℝ) / (r : ℝ) ^ 20 := by
        push_cast
        ring
end BSLambda.LLL
