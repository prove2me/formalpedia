-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dil_bound2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:13.114856+00:00
-- url     : https://prove2.me/submissions/9187486b-8269-4947-91b7-831549b4444a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_rpow_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_W_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_lrt_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_le_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_unit_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_telescope
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_dl
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_dl
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inv_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ne_zero_of_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_Zm_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_Zm_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_Zm_true
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_Zm_false
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_mean_value
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_abs_log_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_abs_log_le_log_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_exp_mem_I
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cc_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_one_le_K
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_adj_sub_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dl_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_unit_lr
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} {A c : ℝ} {m : ℕ} (hA : 0 ≤ A) (hF : CCle A (m + 1) F c) :
    CCle A m (dl t F - F)
      (((4 : ℝ) ^ r) ^ A * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r)) + 2 * r) * (|t.1 - 1| + |t.2 - 1|) * c) := by
  have n1 := ne_zero_of_mem_I h1
  have n2 := ne_zero_of_mem_I h2
  have p1 : 0 < t.1 := by linarith [h1.1]
  have p2 : 0 < t.2 := by linarith [h2.1]
  have hc := cc_nonneg hF
  have hFm : CkOn ((m : ℕ) : ℕ∞) (GV k r) F := ckOn_mono (Nat.le_succ m) hF.1
  have hsub : dl t F - F = dl t F + (-1 : ℂ) • F := by simp [sub_eq_add_neg]
  refine ⟨by rw [hsub]; exact ckOn_add (ckOn_dl t n1 n2 hFm) (ckOn_smul _ hFm), ?_⟩
  intro u v hu hv hlen g hg
  have hun := unit_lr h1 h2 hu hv
  have hL : AllLie (lr u v) := allLie_lr hu hv
  have hl : (lr u v).length ≤ m := by rw [length_lr]; exact hlen
  rw [dLR_eq, W_sub _ hL (ckOn_mono hl (ckOn_dl t n1 n2 hFm)) (ckOn_mono hl hFm) g hg, W_dl t n1 n2]
  show gN g ^ A * ‖W ((lr u v).map (adj t)) F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) - W (lr u v) F g‖ ≤ _
  set κ : ℝ := ((4 : ℝ) ^ r) ^ A with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set δ : ℝ := |t.1 - 1| + |t.2 - 1| with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set g' : Mat k r := (aDil k r t.1)⁻¹ * g * aDil k r t.2 with hg'
  have hg'G : g' ∈ GV k r := dl_mem h1 h2 hg
  set g₂ : Mat k r := g * aDil k r t.2 with hg₂
  have hg₂G : g₂ ∈ GV k r := WeylGroupFacts.uh_mul hg (aDil_mem k r t.2 n2)
  set H : Mat k r → E := W (lr u v) F with hH
  have hH1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H :=
    smooth_on_of_word_derivatives _ hL 1 (ckOn_mono (by omega) hF.1)
  have hpw : pn (lr u v) ≤ 1 := by
    have := pn_le_pow (lr u v) 1 (fun y hy => unit_norm_le (hun y hy))
    simpa using this

  have T1 : gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖ ≤
      κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r * δ) * c)) := by
    have hN : gN g ^ A ≤ κ * gN g' ^ A := by
      have := gN_dil (k := k) (r := r) (inv_mem_I h1) h2 hA g
      rwa [← aDil_inv k r t.1 n1] at this
    have ht := telescope hF hc (one_le_K r) (adj t) (fun _ => rfl) (adj_lie h1 h2) (adj_le h1 h2)
      (adj_sub_le h1 h2) (lr u v) [] (by simp) hun (lrt_lr u v) (by simpa using le_trans hl (Nat.le_succ m))
      g' hg'G
    simp only [List.nil_append] at ht
    have hm : ((lr u v).length : ℝ) ≤ m := by exact_mod_cast hl
    calc gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖
        ≤ (κ * gN g' ^ A) * ‖W ((lr u v).map (adj t)) F g' - H g'‖ :=
          mul_le_mul_of_nonneg_right hN (norm_nonneg _)
      _ = κ * (gN g' ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖) := by ring
      _ ≤ κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r * δ) * c)) :=
          mul_le_mul_of_nonneg_left (le_trans ht (mul_le_mul_of_nonneg_right hm (by positivity))) hκ0

  have T2 : gN g ^ A * ‖H g' - H g₂‖ ≤ κ * (r * c) * |Real.log t.1| := by
    have hB : ∀ σ : ℝ, |σ| ≤ Real.log 2 →
        gN g ^ A * ‖op true (Zm k r) H (cv true (Zm k r) σ g₂)‖ ≤ κ * (r * c) := by
      intro σ hσ
      have hpt : cv true (Zm k r) σ g₂ ∈ GV k r := cv_mem Zm_lie hg₂G σ
      have hN : gN g ^ A ≤ κ * gN (cv true (Zm k r) σ g₂) ^ A := by
        have := gN_dil (k := k) (r := r) (exp_mem_I (by rwa [abs_neg] : |-σ| ≤ Real.log 2)) h2 hA g
        rwa [cv_Zm_true, hg₂, ← Matrix.mul_assoc]
      have hb := bound_scaled hF (lr (Zm k r :: u) v) (lrt_lr _ _)
        (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Zm_lie
          · exact hL x hx)
        (by rw [length_lr, List.length_cons]; omega) _ hpt
      have hpn : pn (lr (Zm k r :: u) v) ≤ r := by
        have e : pn (lr (Zm k r :: u) v) = ‖Zm k r‖ * pn (lr u v) := pn_cons _ _
        rw [e]
        calc ‖Zm k r‖ * pn (lr u v) ≤ r * 1 := mul_le_mul Zm_norm hpw (pn_nonneg _) (by positivity)
          _ = r := by ring
      calc gN g ^ A * ‖op true (Zm k r) H (cv true (Zm k r) σ g₂)‖
          ≤ (κ * gN (cv true (Zm k r) σ g₂) ^ A) * ‖op true (Zm k r) H (cv true (Zm k r) σ g₂)‖ :=
            mul_le_mul_of_nonneg_right hN (norm_nonneg _)
        _ = κ * (gN (cv true (Zm k r) σ g₂) ^ A * ‖W (lr (Zm k r :: u) v) F (cv true (Zm k r) σ g₂)‖) := by
            rw [mul_assoc]; rfl
        _ ≤ κ * (r * c) :=
            mul_le_mul_of_nonneg_left (le_trans hb (mul_le_mul_of_nonneg_right hpn hc)) hκ0
    have h := mean_value hH1 Zm_lie hg₂G true (gN_rpow_nonneg g A) hB (abs_log_le_log_two h1)
    rwa [cv_Zm_true, Real.exp_neg, Real.exp_log p1, ← aDil_inv k r t.1 n1, hg₂, ← Matrix.mul_assoc] at h

  have T3 : gN g ^ A * ‖H g₂ - H g‖ ≤ κ * (r * c) * |Real.log t.2| := by
    have hB : ∀ σ : ℝ, |σ| ≤ Real.log 2 →
        gN g ^ A * ‖op false (Zm k r) H (cv false (Zm k r) σ g)‖ ≤ κ * (r * c) := by
      intro σ hσ
      have hpt : cv false (Zm k r) σ g ∈ GV k r := cv_mem Zm_lie hg σ
      have hN : gN g ^ A ≤ κ * gN (cv false (Zm k r) σ g) ^ A := by
        have := gN_dil (k := k) (r := r) (τ₁ := 1) (by norm_num) (exp_mem_I hσ) hA g
        rwa [aDil_one, Matrix.one_mul, ← cv_Zm_false] at this
      have hsp : lr u v = lr u [] ++ lr [] v := by simp [lr]
      have hsp2 : lr u (Zm k r :: v) = lr u [] ++ (false, Zm k r) :: lr [] v := by simp [lr]
      have hLv : AllLie (lr ([] : List (Mat k r)) v) := allLie_lr (by simp) hv
      have hcomm : op false (Zm k r) H (cv false (Zm k r) σ g) =
          W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g) := by
        rw [hH, hsp, W_append, op_W_comm Zm_lie u (fun X hX => (hu X hX).1) _
          (smooth_on_of_word_derivatives _ hLv _ (ckOn_mono (by rw [length_lr]; simp; omega) hF.1)) _ hpt, hsp2, W_append, W_cons]
      have hb := bound_scaled hF (lr u (Zm k r :: v)) (lrt_lr _ _)
        (by
          intro x hx
          rw [hsp2] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hL x (by rw [hsp]; exact List.mem_append_left _ hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact Zm_lie
            · exact hL x (by rw [hsp]; exact List.mem_append_right _ hx))
        (by rw [length_lr, List.length_cons]; omega) _ hpt
      have hpn : pn (lr u (Zm k r :: v)) ≤ r := by
        have e : pn (lr u (Zm k r :: v)) = ‖Zm k r‖ * pn (lr u v) := by
          rw [hsp2, hsp, pn_append, pn_append, pn_cons]; ring
        rw [e]
        calc ‖Zm k r‖ * pn (lr u v) ≤ r * 1 := mul_le_mul Zm_norm hpw (pn_nonneg _) (by positivity)
          _ = r := by ring
      rw [hcomm]
      calc gN g ^ A * ‖W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g)‖
          ≤ (κ * gN (cv false (Zm k r) σ g) ^ A) * ‖W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g)‖ :=
            mul_le_mul_of_nonneg_right hN (norm_nonneg _)
        _ = κ * (gN (cv false (Zm k r) σ g) ^ A * ‖W (lr u (Zm k r :: v)) F (cv false (Zm k r) σ g)‖) := by
            ring
        _ ≤ κ * (r * c) :=
            mul_le_mul_of_nonneg_left (le_trans hb (mul_le_mul_of_nonneg_right hpn hc)) hκ0
    have h := mean_value hH1 Zm_lie hg false (gN_rpow_nonneg g A) hB (abs_log_le_log_two h2)
    rwa [cv_Zm_false, Real.exp_log p2] at h
  have l1 := abs_log_le h1
  have l2 := abs_log_le h2
  have hrc : 0 ≤ κ * (r * c) := by positivity
  have tri : ‖W ((lr u v).map (adj t)) F g' - H g‖ ≤
      ‖W ((lr u v).map (adj t)) F g' - H g'‖ + ‖H g' - H g₂‖ + ‖H g₂ - H g‖ := by
    have e : W ((lr u v).map (adj t)) F g' - H g =
        (W ((lr u v).map (adj t)) F g' - H g') + (H g' - H g₂) + (H g₂ - H g) := by abel
    rw [e]
    exact norm_add₃_le
  calc gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g‖
      ≤ gN g ^ A * (‖W ((lr u v).map (adj t)) F g' - H g'‖ + ‖H g' - H g₂‖ + ‖H g₂ - H g‖) :=
        mul_le_mul_of_nonneg_left tri (gN_rpow_nonneg g A)
    _ = gN g ^ A * ‖W ((lr u v).map (adj t)) F g' - H g'‖ + gN g ^ A * ‖H g' - H g₂‖ +
          gN g ^ A * ‖H g₂ - H g‖ := by ring
    _ ≤ κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r * δ) * c)) + κ * (r * c) * (2 * |t.1 - 1|) +
          κ * (r * c) * (2 * |t.2 - 1|) :=
        add_le_add (add_le_add T1 (le_trans T2 (mul_le_mul_of_nonneg_left l1 hrc)))
          (le_trans T3 (mul_le_mul_of_nonneg_left l2 hrc))
    _ = κ * (m * ((4 ^ r) ^ (m + 1) * (8 * 4 ^ r)) + 2 * r) * δ * c := by rw [hδ]; ring
end Formalism.FourierDecayAlt.P.B4
