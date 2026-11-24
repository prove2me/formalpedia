-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum_of_separated_cutoff_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:21.94002+00:00
-- url     : https://prove2.me/submissions/04bfbdae-e2fb-4def-a2eb-9886c38d895d

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (h : SeparatedCutoffSum) : GaussianLatticeCutoffSum := by
  intro K abelian₂ hK hLam S
  classical
  let f : GaussianInt → (Unit → ℂ) := fun a _ => (abelian₂ : ℂ) * GaussianInt.toComplex a
  have hf : Function.Injective f := by
    intro a b hab
    have h0 := congrFun hab ()
    simp only [f] at h0
    have hL : (abelian₂ : ℂ) ≠ 0 := by exact_mod_cast hLam.ne'
    exact GaussianInt.toComplex_injective (mul_left_cancel₀ hL h0)
  have hsep : IsNormSeparated abelian₂ (S.image f) := by
    intro D hD D' hD' hne
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hD
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hD'
    have hab : a - b ≠ 0 := fun h0 => hne (by rw [sub_eq_zero.1 h0])
    simp only [Fintype.card_unit, pow_one, Finset.univ_unique, Finset.prod_singleton, f]
    rw [← mul_sub, ← GaussianInt.toComplex_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hLam.le]
    have h1 : (1 : ℝ) ≤ ‖GaussianInt.toComplex (a - b)‖ := by
      have hn : (1 : ℤ) ≤ (a - b).norm := GaussianInt.norm_pos.2 hab
      have h2 : (1 : ℝ) ≤ Complex.normSq (GaussianInt.toComplex (a - b)) := by
        rw [← GaussianInt.intCast_real_norm]; exact_mod_cast hn
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (GaussianInt.toComplex (a - b))]
    nlinarith
  have h3 := h Unit abelian₂ K (fun _ => abelian₂) (S.image f) hLam hK (fun _ => hLam) hsep
  rw [Finset.sum_image (fun a _ b _ hab => hf hab)] at h3
  simp only [Finset.univ_unique, Finset.prod_singleton, max_self, f] at h3
  have e : 4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) * abelian₂ ^ 2 / abelian₂ ^ 2 =
      4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) := by field_simp
  rwa [e] at h3
end Formalism.HermitianLatticeCounting.P
