-- Prove2me | solution 1 for Formalism.ExtensionFiltration.good_bad_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:53:52.380556+00:00
-- url     : https://prove2.me/submissions/a33b5a1c-f0d2-48d8-be54-24b67a611113

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_opNormAt_le
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rk_add
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_ker_cut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_map_cut_le
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_smul_mem_map_cut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rk_map_cut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_bot
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_nPl_ne_zero
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_log_htQ
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rk_mul_mu
import Theorems.Thm_Formalism_HN_height_image_formula
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_size_maximal_slope
import Theorems.Thm_Formalism_HN_slope_characterization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open HermitianIdempotentFrameLemmas
namespace Formalism.ExtensionFiltration
theorem _root_.solution : GoodBadCut := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX e g N hN hg hee hsa hint
  set Ng := N ⊓ (LinearMap.range e).restrictScalars (𝓞 K) with hNg
  set Nb := N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) with hNb
  have hNgfg : Ng.FG := Submodule.FG.of_le hN inf_le_left
  have hNbfg : Nb.FG := Submodule.FG.of_le hN inf_le_left
  have hf : (0 : ℝ) < (nPl K : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm nPl_ne_zero)
  have hg0 : (g : K) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  refine ⟨rk_add b e g N hg hee hint, ?_, ?_⟩
  · set φ : V →ₗ[K] V := (g : K) • (LinearMap.id - e) with hφ
    set I := N.map (φ.restrictScalars (𝓞 K)) with hI
    have hIfg : I.FG := hN.map _
    obtain ⟨hsat, him⟩ := height_image_formula K V ι V ι b X b X hX hX φ N hN
    rw [ker_cut e g hg hee] at hsat him
    have hrk : rkK Nb = rkK I := rk_map_cut e g N hg hee hint
    have hIle : I ≤ Nb := map_cut_le e g N hee hint
    have hIpos := (place_lattice_structure K V ι b X hX I hIfg).2.2
    have hNbpos := (place_lattice_structure K V ι b X hX Nb hNbfg).2.2

    have h1 : ht b X Nb ≤ ht b X I := by
      by_cases hb : Nb = ⊥
      · have : I = Nb := by rw [hb]; exact le_bot_iff.1 (hb ▸ hIle)
        rw [this]
      · have hI0 : I ≠ ⊥ := by
          intro h0
          obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
          have h2 : (g : K) • y ∈ I := smul_mem_map_cut e g N hy
          rw [h0, Submodule.mem_bot] at h2
          exact hy0 ((smul_eq_zero.1 h2).resolve_left hg0)
        exact (size_maximal_slope K V ι b X hX I hIfg hI0).2.2.2.2.2 Nb hIle hNbfg hrk

    have hP0 : 0 ≤ ∏ v, opNormAt b X b X v φ ^ (2 * rkK I) :=
      Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _
    have hP : ∏ v, opNormAt b X b X v φ ^ (2 * rkK I) ≤ (g : ℝ) ^ (nPl K * (2 * rkK I)) := by
      calc ∏ v, opNormAt b X b X v φ ^ (2 * rkK I) ≤ ∏ _v : InfinitePlace K, (g : ℝ) ^ (2 * rkK I) :=
            Finset.prod_le_prod (fun v _ => pow_nonneg (norm_nonneg _) _) fun v _ =>
              pow_le_pow_left₀ (norm_nonneg _) (opNormAt_le b X hX e g v hee (hsa v)) _
        _ = (g : ℝ) ^ (nPl K * (2 * rkK I)) := by
            rw [Finset.prod_const, ← pow_mul, nPl, Finset.card_univ, mul_comm]
    have hQpos : 0 < htQ b X N Ng := by
      by_contra h
      have := mul_nonpos_of_nonneg_of_nonpos hP0 (not_lt.1 h)
      linarith
    have h2 : ht b X Nb ≤ (g : ℝ) ^ (nPl K * (2 * rkK I)) * htQ b X N Ng :=
      h1.trans (him.trans (mul_le_mul_of_nonneg_right hP hQpos.le))
    have h3 := Real.log_le_log hNbpos h2
    rw [Real.log_mul (pow_pos hgR _).ne' hQpos.ne', Real.log_pow,
      log_htQ b X hX N Ng hN hNgfg hsat hQpos] at h3
    rw [rk_mul_mu b X hX N hN, rk_mul_mu b X hX Ng hNgfg, rk_mul_mu b X hX Nb hNbfg, hrk]
    push_cast at h3
    have h4 : -Real.log (ht b X N) ≤ -Real.log (ht b X Ng) + -Real.log (ht b X Nb) +
        (nPl K : ℝ) * (2 * (rkK I : ℝ) * Real.log g) := by linarith
    have h5 := div_le_div_of_nonneg_right h4 hf.le
    rw [add_div, add_div, mul_div_cancel_left₀ _ hf.ne'] at h5
    exact h5
  · intro M hM hNM
    by_cases hb : Nb = ⊥
    · rw [hb, rkK_bot]; simp
    · have hNbM : Nb ≤ M := inf_le_left.trans hNM
      have hM0 : M ≠ ⊥ := fun h => hb (le_bot_iff.1 (h ▸ hNbM))
      have hlat := (place_lattice_structure K V ι b X hX M hM).1
      have hmax := ((slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat hM0).1
        (muMax (Formalism.HermitianLatticesTheory.realize b X) M)).1 le_rfl Nb hNbM
      have hr0 : rk (Formalism.HermitianLatticesTheory.realize b X) Nb ≠ 0 := fun h =>
        hb (((saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat).2.2.2.1 Nb hNbM).1 h)
      have hrpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) Nb : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hr0
      have hs : slope (Formalism.HermitianLatticesTheory.realize b X) Nb ≤ muMax (Formalism.HermitianLatticesTheory.realize b X) M := by
        change deg (Formalism.HermitianLatticesTheory.realize b X) Nb / (rk (Formalism.HermitianLatticesTheory.realize b X) Nb : ℝ) ≤ _
        rw [div_le_iff₀ hrpos]
        exact hmax
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      unfold muDef muMaxDef
      linarith
end Formalism.ExtensionFiltration
