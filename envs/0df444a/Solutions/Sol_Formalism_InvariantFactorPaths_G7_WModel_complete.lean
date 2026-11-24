-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:39.345625+00:00
-- url     : https://prove2.me/submissions/ff8facca-1b45-4d73-8313-ad44a552f420

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_le_one_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_le_pow_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_norm_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.WModel
variable (p : ℕ) [hp : Fact p.Prime]
attribute [local instance] nf
namespace Formalism.InvariantFactorPaths.G7.WModel
theorem _root_.solution : CompleteSpace (KK p) := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have := hp.out.pos
    positivity
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ((p : ℝ)⁻¹) ^ n)
    (fun n => pow_pos hpos n) ?_
  intro u hu
  have h0 : ∀ n, ∃ w : WW p, algebraMap (WW p) (KK p) w = u n - u 0 := fun n =>
    (abv_le_one_iff p _).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, norm_def] at this
      simpa using this.le)
  choose w hw using h0
  have hc : ∀ {m n}, m ≤ n →
      w m ≡ w n [SMOD (Ideal.span {(p : WW p)} ^ m • ⊤ : Submodule (WW p) (WW p))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have := (hu m m n le_rfl hmn).le
    rw [dist_eq_norm, norm_def] at this
    obtain ⟨y, hy⟩ := (abv_le_pow_iff p m _).1 this
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective (WW p) (KK p)
    rw [map_sub, hw, hw, map_mul, map_pow, map_natCast, ← hy]
    ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : WW p)}) w hc
  refine ⟨u 0 + algebraMap (WW p) (KK p) L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  rw [norm_def, abv_le_pow_iff]
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at this
  obtain ⟨y, hy⟩ := this
  refine ⟨y, ?_⟩
  rw [← map_natCast (algebraMap (WW p) (KK p)), ← map_pow, ← map_mul, ← hy, map_sub, hw]
  ring
end Formalism.InvariantFactorPaths.G7.WModel
