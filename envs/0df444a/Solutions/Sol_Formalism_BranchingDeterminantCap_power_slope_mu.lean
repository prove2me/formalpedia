-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.power_slope_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:04.283806+00:00
-- url     : https://prove2.me/submissions/41bd8e98-c896-426a-8152-218645eac6a1

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_rkK_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_eq_bot_of_rkK
import Theorems.Thm_Formalism_BranchingDeterminantCap_orthogonal_sum_slope
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_blockInv
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_majAt_pi
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_majAt_zero_left
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_majAt_zero_right
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_normAt_single
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_rkK_map
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_muMax_mono
import Theorems.Thm_Formalism_F_muMax_mono
import Theorems.Thm_Formalism_F_orthogonal_sum_slope
import Theorems.Thm_Formalism_HN_rerealize


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open OrthogonalSumAlt
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : PowMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A n hA hA0 hn bn Xn An
  have hXn : ∀ v, IsUnit (Xn v).det := fun v =>
    Matrix.isUnit_det_of_right_inverse (blockInv X hX n v)
  let ψ : Fin n → V →ₗ[K] (Fin n → V) := fun i => LinearMap.single K (fun _ : Fin n => V) i
  have hψ : ∀ i, Function.Injective (ψ i) := fun i x y h =>
    Pi.single_injective (M := fun _ : Fin n => V) i h
  let Ai : Fin n → Submodule (𝓞 K) (Fin n → V) := fun i => A.map ((ψ i).restrictScalars (𝓞 K))
  have hAn : (⨆ i, Ai i) = An := by
    change (⨆ i, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => V) i)
      ((fun _ : Fin n => A) i)) = Submodule.pi Set.univ (fun _ : Fin n => A)
    exact Submodule.iSup_map_single
  have hAifg : ∀ i, (Ai i).FG := fun i => hA.map _
  have hAi0 : ∀ i, Ai i ≠ ⊥ := by
    intro i h
    have h1 : Formalism.HN.rkK (Ai i) = Formalism.HN.rkK A := rkK_map (ψ i) (hψ i) A
    rw [h, rkK_bot] at h1
    exact hA0 (eq_bot_of_rkK b h1.symm)
  have hre := fun i => Formalism.HN.rerealize K V ι (Fin n → V) (Σ _ : Fin n, ι) b X bn Xn (ψ i) hX hXn
    (hψ i) (fun v x => normAt_single b X hX n v i x) A hA
  have horth : ∀ s t, s ≠ t → OrthAt bn Xn (Ai s) (Ai t) := by
    rintro s t hst v _ ⟨x, _, rfl⟩ _ ⟨y, _, rfl⟩
    change Formalism.HermitianLatticesTheory.majAt bn Xn v (Pi.single s x) (Pi.single t y) = 0
    rw [majAt_pi b X hX]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = s
    · subst hj
      rw [Pi.single_eq_of_ne hst, majAt_zero_right]
    · rw [Pi.single_eq_of_ne hj, majAt_zero_left]
  obtain ⟨hrk, hdeg, hmu⟩ := orthogonal_sum_slope K (Fin n → V) (Σ _ : Fin n, ι) bn Xn hXn (Fin n) Ai
    hAifg horth
  rw [hAn] at hrk hdeg hmu
  have hrkA : ∀ i, Formalism.HN.rkK (Ai i) = Formalism.HN.rkK A := fun i => rkK_map (ψ i) (hψ i) A
  have hmuA : ∀ i, Formalism.HN.muDef bn Xn (Ai i) = Formalism.HN.muDef b X A := fun i => by
    unfold Formalism.HN.muDef
    rw [(hre i).2.2.1]
  have hmxA : ∀ i, Formalism.HN.muMaxDef bn Xn (Ai i) = Formalism.HN.muMaxDef b X A := fun i => by
    unfold Formalism.HN.muMaxDef
    rw [(hre i).2.2.2.1]
  have hrk' : Formalism.HN.rkK An = n * Formalism.HN.rkK A := by
    rw [hrk]
    simp [hrkA]
  have hr0 : (Formalism.HN.rkK A : ℝ) ≠ 0 := by
    exact_mod_cast fun h => hA0 (eq_bot_of_rkK b h)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hAnfg : An.FG := by
    rw [← hAn]
    exact Submodule.fg_iSup _ hAifg
  have hAn0 : An ≠ ⊥ := by
    intro h
    apply hAi0 ⟨0, hn⟩
    rw [← hAn] at h
    exact le_bot_iff.1 (h ▸ le_iSup Ai ⟨0, hn⟩)
  refine ⟨hrk', ?_, le_antisymm ?_ ?_⟩
  · simp only [degD, hrkA, hmuA, hrk', Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hdeg
    push_cast at hdeg
    have : ((n : ℝ) * (Formalism.HN.rkK A : ℝ)) * Formalism.HN.muDef bn Xn An =
        ((n : ℝ) * (Formalism.HN.rkK A : ℝ)) * Formalism.HN.muDef b X A := by linarith
    exact mul_left_cancel₀ (mul_ne_zero hn0 hr0) this
  · exact hmu _ (fun i _ => (hmxA i).le) hAn0
  · rw [← hmxA ⟨0, hn⟩]
    have := muMax_mono bn Xn hXn (hAifg ⟨0, hn⟩) hAnfg (hAn ▸ le_iSup Ai ⟨0, hn⟩) (hAi0 ⟨0, hn⟩)
    unfold Formalism.HN.muMaxDef
    linarith
end Formalism.BranchingDeterminantCap
