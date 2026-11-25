-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:02.824125+00:00
-- url     : https://prove2.me/submissions/914abf89-7457-4f90-847b-7b4566c549f9

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_slice_prod
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_shape
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_id_shape
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_min_sum_le
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_min_sum_le__5cb92c65a056
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_jetPair_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_C_mul_X_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetsIntegral_subst
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bE_inj
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_change
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_beta_change
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bT_norm_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_bA_norm_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rename_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_minorProd_mem_opInt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_mvExp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
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
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : PairJet.{u} → ThmB.{u} := by
  intro hPJ K _ _ _ pi hpi0 hpi1 H _ _ N0 N1 S u hS hu sg hsg x hx hdet TT colN p hp hp1 I nu1 nu2
    size hn1 hn2 hsz
  classical
  have hdet0 : ∀ τ, (x τ).det ≠ 0 := by
    intro τ h
    have := hdet τ
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set Q : Bool × H → MvPolynomial (Fin N0 × Fin N1) K := fun τ =>
    minorProd (oldRowLow (N1 := N1) (bT x τ)) (p τ) (hp τ) (I τ) with hQ
  have hs : MvPowerSeries.HasSubst (fun z : (Bool × H) × Fin N0 × Fin N1 =>
        (∑ y, MvPowerSeries.C (bA x y z) * MvPowerSeries.X y :
          MvPowerSeries (Bool × H × Fin N0 × Fin N1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => by simp
  have hQint : (∏ τ : Bool × H, rename (fun y => bE H N0 N1 (τ, y)) (Q τ)) ∈
      opInt K (Bool × H × Fin N0 × Fin N1) := by
    refine Subring.prod_mem _ fun τ _ => rename_mem_opInt _ _ ?_
    refine minorProd_mem_opInt _ (fun i b => ?_) _ _ _
    exact Subring.sum_mem _ fun k _ => C_mul_X_mem_opInt _ (bT_norm_le x hx τ i k) _
  rw [op_change x hdet0 colN p hp I, ← jet_pair_linearity K _ _ (bA x), MvPowerSeries.subst_mul hs,
    subst_mvExp hs _ (by simp [MvPowerSeries.smul_eq_C_mul]), MvPowerSeries.subst_smul hs,
    beta_change x hdet0 u]
  refine norm_jetPair_le _ hQint _ _ (Real.rpow_nonneg hpi0.le _) fun κ hκ => ?_
  refine (hPJ K pi hpi0 hpi1 (H × Fin N0 × Fin N1) S (fun i => u i.1) hS (fun i => hu i.1) _
    (jetsIntegral_subst _ (bA_norm_le x hx hdet) sg hsg) κ).trans ?_
  apply Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le
  have hsl := (slice_prod (bE H N0 N1) (bE_inj H N0 N1) Q Finset.univ κ hκ).1
  have key : (∑ i : H × Fin N0 × Fin N1, (min (κ (false, i)) (κ (true, i)) : ℝ)) ≤
      ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun t _ => ?_
    set uf := bSlice (bE H N0 N1) (bE_inj H N0 N1) (false, t) κ with huf
    set ut := bSlice (bE H N0 N1) (bE_inj H N0 N1) (true, t) κ with hut
    have hf := low_shape _ _ _ _ uf (hsl (false, t) (Finset.mem_univ _))
    have hf0 : (∑ y ∈ Finset.univ.filter (fun y : Fin N0 × Fin N1 => y.1.val = 0), uf y) =
        colN (false, t) := by
      refine id_shape (R := K) (p (false, t)) (hp (false, t)) (hp1 (false, t)) (I (false, t)) uf ?_
      have := hsl (false, t) (Finset.mem_univ _)
      simpa [hQ, bT] using this
    have ht := (low_shape _ _ _ _ ut (hsl (true, t) (Finset.mem_univ _))).2
    have e1 : (∑ y : Fin N0 × Fin N1, (min (κ (false, t, y)) (κ (true, t, y)) : ℝ)) =
        ((∑ y, min (uf y) (ut y) : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [e1]
    by_cases h : t ∈ TT
    · simp only [if_pos h]
      have h1 := min_sum_le' (fun y : Fin N0 × Fin N1 => y.1.val = 0) uf ut
      rw [hf0, hf.1, ← hsz, ← hn1] at h1
      have h2 : (∑ y, min (uf y) (ut y)) + nu1 (false, t) ≤ nu1 (true, t) + size (false, t) := by
        rw [hn1 (true, t)]
        omega
      have h3 : ((∑ y, min (uf y) (ut y) : ℕ) : ℝ) + nu1 (false, t) ≤
          nu1 (true, t) + size (false, t) := by exact_mod_cast h2
      have h4 : (0 : ℝ) ≤ nu2 (false, t) := Nat.cast_nonneg _
      linarith
    · simp only [if_neg h]
      have h1 := min_sum_le uf ut
      rw [hf.1, ← hsz] at h1
      have h3 : ((∑ y, min (uf y) (ut y) : ℕ) : ℝ) ≤ size (false, t) := by exact_mod_cast h1
      linarith
  linarith
end Formalism.DworkPowerSeriesWeights
