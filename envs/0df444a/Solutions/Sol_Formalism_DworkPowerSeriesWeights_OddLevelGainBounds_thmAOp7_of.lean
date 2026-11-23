-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAOp7_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:04.466522+00:00
-- url     : https://prove2.me/submissions/eae4289e-6d55-481f-97ec-4f185ad91e05

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGen7Of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_prod_shape
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowOp_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_filter_rows
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution (hJ : ThmAJet7.{u}) : ThmAOp7.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hnl h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT colN p hp hp1 I T hT nu1 nu2 size hnu1 hnu2 hsize spec hspec hinj hframe
  classical
  have hpos : 0 < ‖(l : K)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl.ne_zero
  have h21 : ∀ s, nu2 s ≤ nu1 s := by
    intro s
    rw [hnu1, hnu2]
    exact (Finset.card_le_univ _).trans (by simp)
  have h1s : ∀ s, nu1 s ≤ size s := by
    intro s
    rw [hnu1, hsize]
    calc colN s = ∑ _c : Fin (colN s), 1 := by simp
      _ ≤ ∑ c, p s c := Finset.sum_le_sum fun c _ => hp1 s c
  have hPint : (∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s)) ∈
      opInt K (ZV d N0 N1) :=
    Subring.prod_mem _ fun s _ =>
      minorProd_mem_opInt _ (fun i b => rowOp_mem_opInt TT T hT s i b) _ _ _
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpos.le _)
    fun κ hκ => ?_
  have hsh := op_prod_shape TT T colN p hp hp1 I κ hκ
  have hcap : ∀ (s : ZMod d) (k : Fin N0), ¬ (s ∈ TT ∧ k.val = 0) →
      rowDeg s k κ ≤ capL d TT nu1 nu2 s := by
    intro s k hsk
    unfold capL
    split_ifs with hs
    · rw [hnu2]
      exact ((hsh s).2.2 hs ⟨0, h0⟩ rfl).2 k (fun hk => hsk ⟨hs, hk⟩)
    · rw [hnu1]
      exact (hsh s).2.1 k
  have hjet := hJ K l d N0 N1 hl hl3 hd hde hnl h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT nu1 nu2 size h21 h1s spec κ ?_ ?_ hspec ?_ hcap hframe
  · rw [mul_assoc, norm_mul]
    calc ‖coeff κ (∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s))‖ * _
        ≤ 1 * _ := mul_le_mul_of_nonneg_right (hPint κ) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hjet
  · intro s hs
    rw [hnu1]
    exact ((hsh s).2.2 hs ⟨0, h0⟩ rfl).1
  · intro s
    have hrows := sum_filter_rows
      (fun r : ZMod d × Fin N0 => r.1 = s ∧ ¬ (r.1 ∈ TT ∧ r.2.val = 0)) κ
    refine Eq.trans (Finset.sum_congr ?_ fun _ _ => rfl) (hrows.trans ?_)
    · ext y
      simp [frameTop]
    rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single s]
    · have htot := (hsh s).1
      rw [← hsize] at htot
      unfold Dl
      split_ifs with hs
      · have htop := ((hsh s).2.2 hs ⟨0, h0⟩ rfl).1
        rw [← hnu1] at htop
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, h0⟩ : Fin N0)), htop] at htot
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, h0⟩ : Fin N0))]
        have hrest : (∑ k ∈ Finset.univ.erase (⟨0, h0⟩ : Fin N0),
            if (s = s ∧ ¬ (s ∈ TT ∧ k.val = 0)) then rowDeg s k κ else 0) =
            ∑ k ∈ Finset.univ.erase (⟨0, h0⟩ : Fin N0), rowDeg s k κ := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [if_pos]
          refine ⟨rfl, fun hh => ?_⟩
          exact (Finset.mem_erase.mp hk).1 (Fin.ext hh.2)
        simp only at hrest ⊢
        rw [hrest, if_neg (by simp [hs])]
        omega
      · rw [← htot]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [hs]
    · intro s' _ hs'
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [hs']
    · intro hh
      exact absurd (Finset.mem_univ s) hh
  · intro s0 j
    rw [sum_filter_rows (fun r => spec r = some (s0, j))]
    by_cases hex : ∃ r0, spec r0 = some (s0, j)
    · obtain ⟨r0, hr0⟩ := hex
      have hfil : Finset.univ.filter (fun r => spec r = some (s0, j)) = {r0} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hr
          exact (hinj r0 r (by rw [hr0]; simp) (hr0.trans hr.symm)).symm
        · intro hr
          rw [hr, hr0]
      rw [hfil, Finset.sum_singleton]
      obtain ⟨_, _, hs, hnt, _⟩ := hspec r0.1 r0.2 s0 j hr0
      rw [← hs]
      exact hcap r0.1 r0.2 hnt
    · rw [Finset.filter_false_of_mem (fun r _ hr => hex ⟨r, hr⟩)]
      simp
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
