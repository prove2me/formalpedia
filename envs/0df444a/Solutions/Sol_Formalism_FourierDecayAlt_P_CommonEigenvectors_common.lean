-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CommonEigenvectors.common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:10.209882+00:00
-- url     : https://prove2.me/submissions/7aec3391-c618-43f8-b800-e26d8fcfb6ce

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommonEigenvectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_CommonEigenvectors_eig_in
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CommonEigenvectors
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CommonEigenvectors
theorem _root_.solution [FiniteDimensional ℂ V] {ι : Type} [DecidableEq ι] (D : ι → Module.End ℂ V)
    (hc : ∀ a b, D a * D b = D b * D a) (s : Finset ι) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hst : ∀ a, ∀ x ∈ G, D a x ∈ G) :
    ∃ (G' : Submodule ℂ V) (ν : ι → ℂ), G' ≤ G ∧ G' ≠ ⊥ ∧ (∀ a, ∀ x ∈ G', D a x ∈ G') ∧
      ∀ a ∈ s, ∀ x ∈ G', D a x = ν a • x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨G, 0, le_rfl, hG, hst, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨G₁, ν, h1, h2, h3, h4⟩ := ih
    obtain ⟨μ, x, hx1, hx2, hx3⟩ := eig_in (D a) G₁ h2 (h3 a)
    refine ⟨G₁ ⊓ LinearMap.ker (D a - μ • 1), Function.update ν a μ, le_trans inf_le_left h1, ?_, ?_, ?_⟩
    · intro hbot
      apply hx2
      have hm : x ∈ G₁ ⊓ LinearMap.ker (D a - μ • 1) :=
        Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (by simp [hx3])⟩
      rw [hbot] at hm
      simpa using hm
    · intro c y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      have hcomm : D a (D c y) = D c (D a y) := by
        have := congrArg (fun T => T y) (hc a c)
        simpa using this
      exact Submodule.mem_inf.2 ⟨h3 c y hy1, LinearMap.mem_ker.2 (by simp [hcomm, hy2'])⟩
    · intro b hb y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      rcases Finset.mem_insert.1 hb with rfl | hb
      · simp [hy2']
      · have hba : b ≠ a := fun h => ha (h ▸ hb)
        simp [Function.update_apply, hba, h4 b hb y hy1]
end Formalism.FourierDecayAlt.P.CommonEigenvectors
