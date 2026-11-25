-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.liftOfLoc_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:51:41.966391+00:00
-- url     : https://prove2.me/submissions/45f707b2-965f-4c9d-a5d4-adc54ece9837

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_re_real_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_Nst_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_av_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_block_cross_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_gN_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_len_le_cnt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_mix_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_pair_prob
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_ptSize_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_sum_pair
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution : KB.LiftOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ hpos _ _ hloc
  intro ε hε i s hs hsi hir w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by
    have := len_le_cnt S w.1 v; omega
  have hb1 : 1 ≤ i - s + 1 := by omega
  have hbs : i - s + 1 + s ≤ S.G.r + 1 := by omega
  have hlev : i - s + 1 + s - 1 = i := by omega
  have hi : i ≤ S.G.r + 1 := by omega
  have hwn : w.1.cnt ≤ w.1.cnt + C.Kst := by omega
  have hL := fun v => hloc v (i - s + 1) s hb1 hs hbs (w.1 v) ⟨w, rfl⟩ (hlen v)
  simp only [hlev] at hL
  choose Up θp Um θm hPp hPm hblk using hL
  have hUp : ∀ v, ∀ a ∈ Up v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPp v).2 a ha).1, ((hPp v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hUm : ∀ v, ∀ a ∈ Um v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPm v).2 a ha).1, ((hPm v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hprobP := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θp) (fun v _ => (hPp v).1) (fun v _ => hUp v) hwn hcnt'
  have hprobM := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θm) (fun v _ => (hPm v).1) (fun v _ => hUm v) hwn hcnt'
  refine ⟨fun A x => pθ S A w θp x.1 * pθ S A w θm x.2, fun A => pair_prob (hprobP A) (hprobM A), ?_⟩
  intro Y T κ hY hκ t ht t' ht' ht0 ht0' _ A
  have hσ : ∀ v, S.σ v t ≠ 0 := fun v => (map_ne_zero _).2 ht0
  have hσ' : ∀ v, S.σ v t' ≠ 0 := fun v => (map_ne_zero _).2 ht0'
  have hsz : ∀ v, ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = i - s + 1 - 1 := by
    intro v p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    rw [ptSize_loc, hY h hh]; omega
  have hU : ∀ v, ∃ u : ℂ, ‖u‖ = 1 ∧ (v ∈ A → KB.BlockPSD Y Y
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h'))
      (fun h h' => u * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst *
        KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h'))) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (S.σ v t) (S.σ v t') (Y.image (C.loc (S.σ v))) (hσ v) (hσ' v) (hsz v)
      exact ⟨u, hu, fun _ => blockPSD_comp _ _ _ _ hB Y (C.loc (S.σ v))
        (fun x hx => Finset.mem_image_of_mem _ hx)⟩
    · exact ⟨1, by simp, fun h => absurd h hv⟩
  choose u hu1 hu2 using hU
  have hprod := blockPSD_prod (Y₁ := Y) (Y₂ := Y) univ
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t h')))
    (fun v h h' => (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t' h) (lpt S v s t' h')))
    (by
      intro v _
      by_cases hv : v ∈ A
      · simp only [if_pos hv]; exact hu2 v hv
      · simp only [if_neg hv, one_mul]
        exact blockPSD_pull (Y.image (lpt S v s t) ∪ Y.image (lpt S v s t')) (KB.gN S v ε i (w.1 v))
          (gN_psd S hpos v hε hi w _) Y (lpt S v s t) (lpt S v s t')
          (fun h hh => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))
          (fun h hh => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh)))
  have hmem : ∀ τ ∈ T, ∀ h ∈ Y, TB.join h s τ ∈ TB.pts Y s T := by
    classical
    intro τ hτ h hh
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(h, τ), Finset.mem_product.2 ⟨hh, hτ⟩, rfl⟩
  have hκb : KB.BlockPSD Y Y (TB.blk κ s t t) (TB.blk κ s t t') (TB.blk κ s t' t') :=
    blockPSD_pull (TB.pts Y s T) κ hκ Y (fun h => TB.join h s t) (fun h => TB.join h s t')
      (hmem t ht) (hmem t' ht')
  have hmain := block_cross_le (blockPSD_mul hκb hprod)

  have eL : (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s t t' h h' * ∏ v, (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h')) =
      (∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t' := by
    rw [Nst_eq S hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    simp only [lpt]; ring

  have eD : ∀ (τ : E) (Uq : Fin S.f → Finset (List C.Letter)) (θq : Fin S.f → List C.Letter → ℝ),
      (∀ v, TB.IsProb (Uq v) (θq v)) → (∀ v, ∀ a ∈ Uq v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst) →
      (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s τ τ h h' * ∏ v,
        (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
      ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S A w θq w' : ℂ) * S.base.Nst ε i s w' Y (TB.blk κ s τ τ) τ τ := by
    intro τ Uq θq hP hUq
    have hx : ∀ h h', (∏ v, (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
        ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst),
          (pθ S A w θq w' : ℂ) * ∏ v, KB.gN S v ε i (w'.1 v) (lpt S v s τ h) (lpt S v s τ h') := by
      intro h h'
      have he := expand (A := A) (w := w) (θ := θq) (U := Uq) (fun v _ => hP v) (fun v _ => hUq v) hwn hcnt'
        (fun v a => KB.gN S v ε i a (lpt S v s τ h) (lpt S v s τ h'))
      rw [he, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Complex.ofReal_prod]
      rfl
    simp only [hx]
    rw [mix_sum]
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Nst_eq S hi]; rfl
  have hK : S.base.K = C.Kst := rfl
  have hcw : S.base.cnt w = w.1.cnt := rfl
  rw [eL, eD t Up θp (fun v => (hPp v).1) hUp, eD t' Um θm (fun v => (hPm v).1) hUm, re_real_sum, re_real_sum]
    at hmain
  have hsp := sum_pair (S.base.Wb (w.1.cnt + C.Kst)) (S.base.Wb (w.1.cnt + C.Kst)) (pθ S A w θp) (pθ S A w θm)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t t) t t).re)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t' t') t' t').re) (hprobM A).2.2 (hprobP A).2.2
  rw [hK, hcw, hsp]
  calc (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ C.Kst) * ‖S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ =
      ‖(∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ := by
        rw [norm_mul, norm_prod]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [norm_mul, hu1, one_mul, norm_pow, av_eq, map_sub, map_inv₀, map_inv₀]
    _ ≤ _ := hmain
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.PBA
