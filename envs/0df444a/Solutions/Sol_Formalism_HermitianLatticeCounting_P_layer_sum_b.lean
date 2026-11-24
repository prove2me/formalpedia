-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.layer_sum_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:30.004443+00:00
-- url     : https://prove2.me/submissions/07841dab-34a7-4707-96a2-464cc55ad38d

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Classical
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (ι Γ : Type) [Fintype ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B K : ℝ)
    (F : ℝ → ℝ) (u w : ℕ → ℝ) (hA : 0 ≤ A) (hu : ∀ i, 0 ≤ u i) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ t, 0 ≤ F t) (hlev : ∀ t, 0 ≤ t → ∃ i, t ≤ u i ∧ F t ≤ w i)
    (hd : ∀ γ ∈ S, ∀ v, 0 ≤ d γ v)
    (hcount : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v))
    (hK : ∀ M, ∑ i ∈ range M, w i * Real.exp (B * u i) ≤ K) :
    ∑ γ ∈ S, ∏ v, F (d γ v) ≤ A * K ^ Fintype.card ι := by
  have hlev' : ∀ t : ℝ, ∃ i, 0 ≤ t → (t ≤ u i ∧ F t ≤ w i) := by
    intro t
    by_cases ht : 0 ≤ t
    · obtain ⟨i, hi⟩ := hlev t ht
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose lev hl using hlev'
  set L : Γ → ι → ℕ := fun γ v => lev (d γ v) with hL
  set M : ℕ := (S.sup fun γ => univ.sup (L γ)) + 1 with hM
  set T : Finset (ι → ℕ) := Fintype.piFinset fun _ => range M with hT
  have hmaps : ∀ γ ∈ S, L γ ∈ T := by
    intro γ hγ
    rw [hT, Fintype.mem_piFinset]
    intro v
    rw [mem_range, hM, Nat.lt_succ_iff]
    exact le_trans (Finset.le_sup (f := L γ) (mem_univ v))
      (Finset.le_sup (f := fun γ => univ.sup (L γ)) hγ)
  have h1 : ∑ γ ∈ S, ∏ v, F (d γ v) ≤ ∑ γ ∈ S, ∏ v, w (L γ v) := by
    apply Finset.sum_le_sum
    intro γ hγ
    apply Finset.prod_le_prod
    · intro v _; exact hF _
    · intro v _; exact (hl _ (hd γ hγ v)).2
  have h2 : ∑ γ ∈ S, ∏ v, w (L γ v) = ∑ I ∈ T, ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h3 : ∀ I ∈ T, ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) ≤
      A * ∏ v, (w (I v) * Real.exp (B * u (I v))) := by
    intro I _
    have e1 : ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) = ((S.filter fun γ => L γ = I).card : ℝ) * ∏ v, w (I v) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [(Finset.mem_filter.1 hγ).2]
    rw [e1]
    have hsub : (S.filter fun γ => L γ = I) ⊆ (S.filter fun γ => ∀ v, d γ v ≤ u (I v)) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ ⊢
      refine ⟨hγ.1, fun v => ?_⟩
      rw [← hγ.2]
      exact (hl _ (hd γ hγ.1 v)).1
    have hc : ((S.filter fun γ => L γ = I).card : ℝ) ≤ A * Real.exp (B * ∑ v, u (I v)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) (hcount _ fun v => hu _)
    have hp : 0 ≤ ∏ v, w (I v) := Finset.prod_nonneg fun v _ => hw _
    calc _ ≤ A * Real.exp (B * ∑ v, u (I v)) * ∏ v, w (I v) := mul_le_mul_of_nonneg_right hc hp
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]; ring
  have h4 : ∑ I ∈ T, A * ∏ v, (w (I v) * Real.exp (B * u (I v))) =
      A * (∑ i ∈ range M, w i * Real.exp (B * u i)) ^ Fintype.card ι := by
    have := Finset.prod_univ_sum (fun _ : ι => range M) (fun _ i => w i * Real.exp (B * u i))
    rw [← Finset.mul_sum, hT, ← this, Finset.prod_const, Finset.card_univ]
  have h5 : 0 ≤ ∑ i ∈ range M, w i * Real.exp (B * u i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := Finset.sum_le_sum h3
    _ = _ := h4
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact pow_le_pow_left₀ h5 (hK M) _
end Formalism.HermitianLatticeCounting.P
