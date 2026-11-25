-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.equivariant_operators_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:06.7645+00:00
-- url     : https://prove2.me/submissions/ef9731de-ee0c-4092-a216-e5a7929aeb83

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableEquivOps
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_level_zero_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_mat_inv_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_FFS_rho_pOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_one_mem_UW
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open Formalism.QuantumDeterminants.WeylGroupFacts
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution : EquivOps := by
  intro hE k r Wp Wq _ _ _ _ _ D O P hDom hloc hsmul hsm hcomm J hJ
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  have hext : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → ∃ (f : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)),
      B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ IsOpen U ∧ g₀ ∈ U ∧
        ∀ x ∈ U, x ∈ B.GV k r → f x = J x :=
    fun g₀ hg hO => hE k r (Wq →L[ℂ] Wp) O J hDom.1 hS g₀ hg hO
  have one_N : (1 : B.Mat k r) ∈ Q.Nlev k r 0 := ⟨mem_n_one, (level_zero_iff _).2 uh_one⟩
  have one_S : ∀ z, (1 : B.Mat k r) ∈ Q.Slev k r z 0 :=
    fun z => ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, one_N, by simp⟩
  have hπ1 : D.π 1 = 1 := D.π_rep.1
  have hπ'1 : D.π' 1 = 1 := D.π'_rep.1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro g₀ hg₀
    have hgG := (level_zero_iff g₀).1 hg₀.1
    obtain ⟨f, U, hf, _, hfO, hUo, hgU, hfJ⟩ := hext g₀ hgG hg₀.2
    obtain ⟨U', F, hU', hgU', hF, hFe⟩ := hsm f hf hfO g₀ hg₀
    refine ⟨U ∩ U', F, hUo.inter hU', ⟨hgU, hgU'⟩, hF.mono Set.inter_subset_right, ?_⟩
    intro x hx hxG
    rw [← hFe x hx.2 hxG]
    exact hloc U J f hUo (fun y hy hyG => (hfJ y hy hyG).symm) x hx.1 ((level_zero_iff x).1 hxG)
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hng : n * g ∈ O := by
      have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z, n, hn, by simp⟩ 1 (one_S D.z')
      simpa using this
    have hngG : n * g ∈ B.GV k r := uh_mul hnG hgG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hngU1, hf1J⟩ := hext (n * g) hngG hng
    have hp : D.inSS (pOf 1 n⁻¹ 1 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_inv hnN
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 n⁻¹ 1 1) F = fun x => F (n * x) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv n (isUnit_of_uh hnG), mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (n * g) = P J (n * g) := hloc U1 f1 J hU1 hf1J (n * g) hngU1 hngG
    have hV : IsOpen ((fun x : B.Mat k r => n * x) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_const.matrix_mul continuous_id)).inter hDom.1
    have e2 : P (fun x => f1 (n * x)) g = P (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hngU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (n * x) hx.1 (uh_mul hnG hxG), Pi.smul_apply]
      exact hL x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hgn : g * n ∈ O := by
      have := hDom.2 g hg 1 (one_S D.z) n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z', n, hn, by simp⟩
      simpa using this
    have hgnG : g * n ∈ B.GV k r := uh_mul hgG hnG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hgnU1, hf1J⟩ := hext (g * n) hgnG hgn
    have hp : D.inSS (pOf 1 1 1 n) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_one
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact hnN
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 1 1 n) F = fun x => F (x * n) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (g * n) = P J (g * n) := hloc U1 f1 J hU1 hf1J (g * n) hgnU1 hgnG
    have hV : IsOpen ((fun x : B.Mat k r => x * n) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_id.matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => f1 (x * n)) g = P (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hgnU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (x * n) hx.1 (uh_mul hxG hnG), Pi.smul_apply]
      exact hR x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg h hh h' hh'
    have hgG := (level_zero_iff g).1 hg.1
    have hhG : h ∈ B.GV k r := hh.1
    have hh'G : h' ∈ B.GV k r := hh'.1
    have hu := isUnit_of_uh hhG
    have hu' := isUnit_of_uh hh'G
    have hhg : h * g * h' ∈ O := by
      have := hDom.2 g hg h ⟨h, hh, 1, one_N, by simp⟩ h' ⟨h', hh', 1, one_N, by simp⟩
      simpa using this
    have hhgG : h * g * h' ∈ B.GV k r := uh_mul (uh_mul hhG hgG) hh'G
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hhgU1, hf1J⟩ := hext (h * g * h') hhgG hhg
    have hp : D.inSS (pOf h⁻¹ 1 h' 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact uw_inv hh
      · exact mem_n_one
      · exact hh'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf h⁻¹ 1 h' 1) F =
        fun x => (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹)) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv h hu, mat_inv_one]
      simp [Matrix.mul_assoc]

    have eL : (D.π h⁻¹).comp (D.π h) = 1 := by
      rw [← D.π_rep.2 _ (uw_inv hh) _ hh, Matrix.nonsing_inv_mul h hu, hπ1]
    have eL' : (D.π h).comp (D.π h⁻¹) = 1 := by
      rw [← D.π_rep.2 _ hh _ (uw_inv hh), Matrix.mul_nonsing_inv h hu, hπ1]
    have eR : (D.π' h').comp (D.π' h'⁻¹) = 1 := by
      rw [← D.π'_rep.2 _ hh' _ (uw_inv hh'), Matrix.mul_nonsing_inv h' hu', hπ'1]
    have eR' : (D.π' h'⁻¹).comp (D.π' h') = 1 := by
      rw [← D.π'_rep.2 _ (uw_inv hh') _ hh', Matrix.nonsing_inv_mul h' hu', hπ'1]
    have eLv : ∀ w, D.π h⁻¹ (D.π h w) = w := fun w => by simpa using congrArg (fun L => L w) eL
    have eL'v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eL'
    have eRv : ∀ w, D.π' h' (D.π' h'⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eR
    have eR'v : ∀ w, D.π' h'⁻¹ (D.π' h' w) = w := fun w => by simpa using congrArg (fun L => L w) eR'
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    have e1 : P f1 (h * g * h') = P J (h * g * h') := hloc U1 f1 J hU1 hf1J _ hhgU1 hhgG
    have hV : IsOpen ((fun x : B.Mat k r => h * x * h') ⁻¹' U1 ∩ O) :=
      (hU1.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => (D.π h⁻¹).comp ((f1 (h * x * h')).comp (D.π' h'⁻¹))) g = P J g := by
      refine hloc _ _ _ hV ?_ g ⟨hhgU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J _ hx.1 (uh_mul (uh_mul hhG hxG) hh'G), hU x ⟨(level_zero_iff x).2 hxG, hx.2⟩ h hh h' hh']
      ext v
      simp [eLv, eRv]
    rw [e2] at hc
    beta_reduce at hc
    rw [e1] at hc

    rw [hc]
    ext v
    simp [eL'v, eR'v]
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
