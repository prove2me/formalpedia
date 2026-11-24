-- Prove2me | solution 1 for Formalism.UG.P.wlocal_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:27:39.110364+00:00
-- url     : https://prove2.me/submissions/3ff4f850-83b5-436b-aedd-f0d3263bd9e1

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_UG_P_wlocal_map_applyWord
import Theorems.Thm_Formalism_UG_P_wlocal_map_hw
import Theorems.Thm_Formalism_UG_P_wlocal_map_smul
import Theorems.Thm_Formalism_UG_P_wlocal_kill
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution (P : Ideal R) [P.IsPrime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (x : MvPolynomial (Fin r × Fin n) R)
    (hx : map (algebraMap R (Localization.AtPrime P)) x ∈ weyl (Localization.AtPrime P) r n hn ν) :
    ∃ t ∈ P.primeCompl, C t * x ∈ weyl R r n hn ν := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* Localization.AtPrime P, φ = algebraMap R (Localization.AtPrime P) :=
    ⟨_, rfl⟩
  rw [← hφ] at hx
  have key : ∀ y ∈ weyl (Localization.AtPrime P) r n hn ν,
      ∃ s ∈ P.primeCompl, ∃ z ∈ weyl R r n hn ν, φ s • y = map φ z := by
    intro y hy
    unfold weyl at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro y' hy'
      obtain ⟨w, rfl⟩ := hy'
      refine ⟨1, P.primeCompl.one_mem, applyWord R w (hw R hn ν), ?_, ?_⟩
      · unfold weyl
        exact Submodule.subset_span ⟨w, rfl⟩
      · rw [map_one, one_smul, wlocal_map_applyWord, wlocal_map_hw]
    · exact ⟨1, P.primeCompl.one_mem, 0, Submodule.zero_mem _, by simp⟩
    · intro y1 y2 _ _ h1 h2
      obtain ⟨s1, hs1, z1, hz1, e1⟩ := h1
      obtain ⟨s2, hs2, z2, hz2, e2⟩ := h2
      refine ⟨s1 * s2, P.primeCompl.mul_mem hs1 hs2, s2 • z1 + s1 • z2,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hz1) (Submodule.smul_mem _ _ hz2), ?_⟩
      rw [map_add, wlocal_map_smul, wlocal_map_smul, ← e1, ← e2]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    · intro a y' _ h
      obtain ⟨s, hs, z, hz, e⟩ := h
      obtain ⟨⟨b, s'⟩, hbs0⟩ := IsLocalization.mk'_surjective P.primeCompl a
      have hbs : IsLocalization.mk' (Localization.AtPrime P) b s' = a := hbs0
      refine ⟨(s' : R) * s, P.primeCompl.mul_mem s'.2 hs, b • z, Submodule.smul_mem _ _ hz, ?_⟩
      have hspec : φ (s' : R) * IsLocalization.mk' (Localization.AtPrime P) b s' = φ b := by
        rw [hφ]
        first
        | exact IsLocalization.mk'_spec' (S := Localization.AtPrime P) b s'
        | simp
      rw [wlocal_map_smul, ← e, ← hbs, ← hspec, map_mul, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨s, hs, z, hz, e⟩ := key _ hx
  have h0 : map φ (C s * x - z) = 0 := by
    rw [map_sub, map_mul, map_C, ← e, MvPolynomial.smul_eq_C_mul, sub_self]
  obtain ⟨t, ht, htz⟩ := wlocal_kill P (C s * x - z) (by rw [← hφ]; exact h0)
  refine ⟨t * s, P.primeCompl.mul_mem ht hs, ?_⟩
  have h1 : C (t * s) * x = t • z := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    linear_combination htz
  rw [h1]
  exact Submodule.smul_mem _ _ hz
end Formalism.UG.P
