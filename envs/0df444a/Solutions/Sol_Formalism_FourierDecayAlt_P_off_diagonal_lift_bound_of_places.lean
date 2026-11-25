-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.off_diagonal_lift_bound_of_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:42.423847+00:00
-- url     : https://prove2.me/submissions/dcb16a92-25f6-45fc-a4ca-40ff52810084

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JCx1_norm___ca49aaa707bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_psd_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_join_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_nst_diag_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_nst_gram
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_minFac_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_combine
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism.FourierDecayAlt.P.JCx1.decay Formalism.FourierDecayAlt.TB
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.OffDiagonalLiftBoundOfPlaces := by
  intro hP3 hGP hWP E _ _ _ Wp Wq _ _ _ _ S abelian₂ Lam' hPos hGr hBelow hTop hThr
  have hG : S.base.GramPSD := hGP E Wp Wq S hPos hGr _ _ _ _
  have hW : S.base.WordsPos := hWP E Wp Wq S hGr _ _ _ _
  intro ε hε i s hs hsi hir hns w hw hcnt
  have hir' : i ≤ S.G.r + 1 := hir
  have hav : ∀ v (x : E), x ≠ 0 → 0 < S.base.av v x := fun v x hx => by
    show 0 < S.pl v x
    exact (S.pl v).pos_iff.mpr hx
  by_cases hi : i ≤ S.G.r
  · obtain ⟨θ, hθ, hb⟩ := hBelow ε hε i s hs hsi hi w hw hcnt
    refine ⟨fun (π : Fin S.f → Fin 3) => θ (univ.filter fun v => π v ≠ 0), fun π => hθ _, ?_⟩
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho
    refine ⟨fun v => if S.base.szL (i - s + 1) s v < S.base.av v (t⁻¹ - t'⁻¹) then 1 else 0, ?_⟩
    have hthr : ∀ v, 0 ≤ abelian₂ (i - s + 1) s v ∧ abelian₂ (i - s + 1) s v ≤ S.base.szL (i - s + 1) s v :=
      fun v => hThr.1 (i - s + 1) s (by omega) hs (by omega) v
    have hM : ∀ A, 0 ≤ ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K),
        θ A x * (((S.base.Nst ε i s x.1 Y (blk κ s t t) t t).re +
          (S.base.Nst ε i s x.2 Y (blk κ s t' t') t' t').re) / 2) := fun A =>
      Finset.sum_nonneg fun x _ => mul_nonneg ((hθ A).1 x) (div_nonneg (add_nonneg
        (nst_diag_nonneg _ hG hW hε i s x.1 Y T κ hκ t ht)
        (nst_diag_nonneg _ hG hW hε i s x.2 Y T κ hκ t' ht')) zero_le_two)
    exact combine S.base.K (abelian₂ (i - s + 1) s) (S.base.szL (i - s + 1) s) (fun v => S.base.av v (t⁻¹ - t'⁻¹))
      _ _ _ (fun v => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with h <;> simp [h])
      (fun v => (hthr v).1) (fun v => (hthr v).2) (fun v => hav v _ ho) (hM _)
      (hb Y T κ hY hκ t ht t' ht' h0 h0' ho _)
  · have hi' : i = S.G.r + 1 := by omega
    subst hi'
    have hs2 : 2 ≤ s := by
      by_contra hc
      exact hns ⟨rfl, by omega⟩
    obtain ⟨θ, hθ, hb⟩ := hTop ε hε s hs2 hsi w hw hcnt
    have hbs : S.G.r + 1 - s + 1 = S.G.r + 2 - s := by omega
    rw [hbs]
    let θ2 : (Fin S.f → Fin 3) → S.W × S.W → ℝ := fun π x =>
      θ (univ.filter fun v => π v = 1) x.1 * θ (univ.filter fun v => π v = 2) x.2
    refine ⟨θ2, fun π => ⟨fun x => mul_nonneg ((hθ _).1 _) ((hθ _).1 _), fun x hx => ?_, ?_⟩, ?_⟩
    · rw [Finset.mem_product, not_and_or] at hx
      rcases hx with hx | hx
      · simp only [θ2, (hθ _).2.1 _ hx, zero_mul]
      · simp only [θ2, (hθ _).2.1 _ hx, mul_zero]
    · simp only [θ2]
      rw [Finset.sum_product, ← Finset.sum_mul_sum, (hθ _).2.2, (hθ _).2.2, one_mul]
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho
    let tv : Fin S.f → ℂ := fun v => S.σ v t
    let tv' : Fin S.f → ℂ := fun v => S.σ v t'
    let L : Fin S.f → ℝ := Lam' (S.G.r + 2 - s) s
    have hthr : ∀ v, 0 ≤ L v ∧ 2 * L v ≤ S.base.szL (S.G.r + 2 - s) s v :=
      fun v => hThr.2 s hs2 hsi v
    have hoA : ∀ v, PairingProductCorollary.oAbs tv tv' v = S.base.av v (t⁻¹ - t'⁻¹) := fun v => by
      simp only [PairingProductCorollary.oAbs, tv, tv', one_div, ← map_inv₀, ← map_sub]
      exact Formalism.FourierDecayAlt.P.JCx1.norm_σ S v _
    have htv : ∀ v, ‖tv v‖ = S.base.av v t := fun v => Formalism.FourierDecayAlt.P.JCx1.norm_σ S v _
    let π : Fin S.f → Fin 3 := fun v =>
      if 2 * L v < PairingProductCorollary.oAbs tv tv' v then (if ‖tv v‖ ≤ ‖tv' v‖ then 1 else 2) else 0
    refine ⟨π, ?_⟩
    have hY' : ∀ h ∈ Y, TB.level h = S.G.r + 1 - s := hY
    have hκt : PSDOn Y (blk κ s t t) := by
      classical
      exact psd_pull _ κ hκ Y (fun h => join h s t) (join_mem Y s T t ht)
    have hκt' : PSDOn Y (blk κ s t' t') := by
      classical
      exact psd_pull _ κ hκ Y (fun h => join h s t') (join_mem Y s T t' ht')
    set B1 : Finset (Fin S.f) := univ.filter fun v => π v = 1 with hB1
    set B2 : Finset (Fin S.f) := univ.filter fun v => π v = 2 with hB2
    set S1 := ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θ B1 w' *
      (S.base.Nst ε (S.G.r + 1) s w' Y (blk κ s t t) t t).re with hS1
    set S2 := ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θ B2 w' *
      (S.base.Nst ε (S.G.r + 1) s w' Y (blk κ s t' t') t' t').re with hS2
    have hS1n : 0 ≤ S1 := Finset.sum_nonneg fun x _ =>
      mul_nonneg ((hθ _).1 x) (nst_diag_nonneg _ hG hW hε _ s x Y T κ hκ t ht)
    have hS2n : 0 ≤ S2 := Finset.sum_nonneg fun x _ =>
      mul_nonneg ((hθ _).1 x) (nst_diag_nonneg _ hG hW hε _ s x Y T κ hκ t' ht')
    have e1 : univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ‖tv v‖ ≤ ‖tv' v‖) = B1 := by
      ext v
      simp only [hB1, π, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    have e2 : univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ¬ ‖tv v‖ ≤ ‖tv' v‖) = B2 := by
      ext v
      simp only [hB2, π, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp_all
    have hB1b : (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t t) t t).re ≤
        (∏ v ∈ univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ‖tv v‖ ≤ ‖tv' v‖),
          (‖tv v‖ * L v) ^ (2 * S.base.K)) * S1 := by
      rw [e1]
      have := hb Y hY' (blk κ s t t) hκt t h0 B1
      simpa only [htv] using this
    have hB2b : (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t' t') t' t').re ≤
        (∏ v ∈ univ.filter (fun v => 2 * L v < PairingProductCorollary.oAbs tv tv' v ∧ ¬ ‖tv v‖ ≤ ‖tv' v‖),
          (‖tv' v‖ * L v) ^ (2 * S.base.K)) * S2 := by
      rw [e2]
      have := hb Y hY' (blk κ s t' t') hκt' t' h0' B2
      have htv' : ∀ v, ‖tv' v‖ = S.base.av v t' := fun v => Formalism.FourierDecayAlt.P.JCx1.norm_σ S v _
      simpa only [htv'] using this
    have hmain := hP3 (Fin S.f) S.base.K L tv tv' (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t t') t t')
      (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t t) t t).re
      (S.base.Nst ε (S.G.r + 1) s w Y (blk κ s t' t') t' t').re S1 S2
      (fun v => ⟨(map_ne_zero (S.σ v)).mpr h0, (map_ne_zero (S.σ v)).mpr h0'⟩) (fun v => (hthr v).1)
      (nst_diag_nonneg _ hG hW hε _ s w Y T κ hκ t ht) (nst_diag_nonneg _ hG hW hε _ s w Y T κ hκ t' ht')
      hS1n hS2n (nst_gram _ hG hW hε _ s w Y T κ hκ t t' ht ht') hB1b hB2b
    have hsum : ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θ2 π x *
        (((S.base.Nst ε (S.G.r + 1) s x.1 Y (blk κ s t t) t t).re +
          (S.base.Nst ε (S.G.r + 1) s x.2 Y (blk κ s t' t') t' t').re) / 2) = (S1 + S2) / 2 := by
      rw [Finset.sum_product]
      simp only [θ2, ← hB1, ← hB2]
      have hsplit : ∀ x y : S.W, θ B1 x * θ B2 y *
          (((S.base.Nst ε (S.G.r + 1) s x Y (blk κ s t t) t t).re +
            (S.base.Nst ε (S.G.r + 1) s y Y (blk κ s t' t') t' t').re) / 2) =
          (θ B1 x * (S.base.Nst ε (S.G.r + 1) s x Y (blk κ s t t) t t).re) * θ B2 y / 2 +
            θ B1 x * (θ B2 y * (S.base.Nst ε (S.G.r + 1) s y Y (blk κ s t' t') t' t').re) / 2 := by
        intro x y; ring
      simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul_sum, hS1, hS2,
        (hθ B1).2.2, (hθ B2).2.2, mul_one, one_mul]
      ring
    rw [hsum]
    refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine Finset.prod_le_prod (fun v _ => ?_) (fun v _ => ?_)
    · unfold PairingProductCorollary.minFac; split_ifs
      · exact pow_nonneg (div_nonneg (by linarith [(hthr v).1]) (norm_nonneg _)) _
      · exact zero_le_one
    · have hpos : 0 < PairingProductCorollary.oAbs tv tv' v := by rw [hoA]; exact hav v _ ho
      rw [minFac_eq _ _ _ (by linarith [(hthr v).1]) hpos, hoA]
      refine min_le_min_left _ (pow_le_pow_left₀ (div_nonneg (by linarith [(hthr v).1]) (hav v _ ho).le) ?_ _)
      exact div_le_div_of_nonneg_right (hthr v).2 (hav v _ ho).le
end Formalism.FourierDecayAlt.P
