-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.t_TraceDual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:16.025665+00:00
-- url     : https://prove2.me/submissions/fb1a705f-b59d-46fa-9065-65c79bbf3bac

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_t_TracePairing
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_semb_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_orth_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution : TraceDual := by
  have hT := t_TracePairing
  intro E _ _ _ L g c hg hc hL μ
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hμ

    let R : E →ₗ[ℚ] ℝ := ((innerₗ (CV E) μ).toAddMonoidHom.comp (semb E c)).toRatLinearMap
    have hR : ∀ x, R x = inner ℝ μ (semb E c x) := fun x => rfl
    let b := Module.finBasis ℚ E
    have hq : ∀ j, ∃ q : ℚ, R (b j) = (q : ℝ) := by
      intro j
      obtain ⟨n, hn, hnL⟩ := hL (b j)
      have h1 := hμ (semb E c ((n : E) * b j)) (Submodule.mem_map_of_mem (f := (semb E c).toIntLinearMap) hnL)
      obtain ⟨m, hm⟩ := Submodule.mem_one.mp h1
      have h2 : R ((n : E) * b j) = (n : ℝ) * R (b j) := by
        have : (n : E) * b j = (n : ℚ) • b j := by rw [Algebra.smul_def]; simp
        rw [this, map_smul]; simp [Rat.smul_def]
      refine ⟨(m : ℚ) / n, ?_⟩
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have h3 : (n : ℝ) * R (b j) = (m : ℝ) := by
        rw [← h2, hR]; exact hm.symm.trans (by simp)
      push_cast
      field_simp
      linarith
    choose q hq using hq
    let lam : E →ₗ[ℚ] ℚ := b.constr ℚ q
    have hlam : ∀ x, R x = ((lam x : ℚ) : ℝ) := by
      intro x
      have : R = (Algebra.linearMap ℚ ℝ).comp lam := by
        apply b.ext
        intro j
        simp [lam, hq]
      rw [this]; simp
    have hnd := traceForm_nondegenerate ℚ E
    let l' : E := (LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm lam
    have hl' : ∀ x, Algebra.trace ℚ E (l' * x) = lam x := by
      intro x
      have := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm ℚ E) (hB := hnd) lam x
      rw [Algebra.traceForm_apply] at this
      exact this
    have hl : ∀ x, Algebra.trace ℚ E ((g : E) * l' * x / g) = lam x := by
      intro x
      rw [← hl' x]; congr 1; field_simp
    refine ⟨(g : E) * l', ?_, ?_⟩
    · intro y hy
      have h1 := hμ (semb E c y) (Submodule.mem_map_of_mem (f := (semb E c).toIntLinearMap) hy)
      obtain ⟨m, hm⟩ := Submodule.mem_one.mp h1
      refine ⟨m, ?_⟩
      rw [hl y]
      have : ((lam y : ℚ) : ℝ) = (m : ℝ) := by
        rw [← hlam, hR]; exact hm.symm.trans (by simp)
      have h5 : (lam y : ℚ) = (m : ℚ) := by exact_mod_cast this
      rw [h5]; simp
    · have : dm E g c ((g : E) * l') - μ = 0 := by
        apply orth_zero
        intro t
        have h1 := hT E g c ((g : E) * l') t hg hc
        rw [hl t, ← hlam, hR] at h1
        have h2 : inner ℝ (dm E g c ((g : E) * l') - μ) (semb E c t) = 0 := by
          rw [inner_sub_left, h1, sub_self]
        rw [semb_apply E c t, inner_smul_right] at h2
        exact (mul_eq_zero.mp h2).resolve_left hc
      exact sub_eq_zero.mp this
  · rintro ⟨l, hl, rfl⟩ y hy
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨m, hm⟩ := hl t ht
    rw [Submodule.mem_one]
    refine ⟨m, ?_⟩
    have := hT E g c l t hg hc
    show _ = inner ℝ (dm E g c l) (semb E c t)
    rw [this, ← hm]; simp
end Formalism.FourierDecayAlt.P.Jx3
