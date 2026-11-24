-- Prove2me | solution 1 for Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:15.351662+00:00
-- url     : https://prove2.me/submissions/1b3acbbb-52d9-4d79-a049-999a6e16c622

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_EigenDecomposition
import Theorems.Thm_Formalism_IndefR_EigenDecomposition_exists_onb_of_parts_set
import Theorems.Thm_Formalism_IndefR_EigenDecomposition_reIm_isSymmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Formalism Formalism.IndefR Formalism.IndefR.EigenDecomposition
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.IndefR.EigenDecomposition
theorem _root_.solution (A : Set (H →ₗ[ℂ] H))
    (hcomm : ∀ S ∈ A, ∀ T ∈ A, Commute S T)
    (hadj : ∀ T ∈ A, LinearMap.adjoint T ∈ A) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ H), ∀ k, ∀ T ∈ A, ∃ μ : ℂ, T (b k) = μ • b k := by
  classical
  obtain ⟨B, hBA, hspan, hli⟩ := exists_linearIndependent ℂ A
  have hBfin : B.Finite := hli.setFinite
  have : Fintype B := hBfin.fintype
  have r1 : ∀ S : H →ₗ[ℂ] H, reIm S true = S + LinearMap.adjoint S := fun S => by simp [reIm]
  have r2 : ∀ S : H →ₗ[ℂ] H, reIm S false = Complex.I • (S - LinearMap.adjoint S) :=
    fun S => by simp [reIm]

  have cl : ∀ (S X : H →ₗ[ℂ] H) (β : Bool), Commute S X → Commute (LinearMap.adjoint S) X →
      Commute (reIm S β) X := by
    intro S X β h1 h2
    cases β
    · rw [r2]; exact (h1.sub_left h2).smul_left _
    · rw [r1]; exact h1.add_left h2
  have cr : ∀ (S X : H →ₗ[ℂ] H) (β : Bool), Commute X S → Commute X (LinearMap.adjoint S) →
      Commute X (reIm S β) := fun S X β h1 h2 => (cl S X β h1.symm h2.symm).symm
  have hc : ∀ S ∈ A, ∀ S' ∈ A, ∀ β β', Commute (reIm S β) (reIm S' β') := by
    intro S hS S' hS' β β'
    exact cl _ _ _ (cr _ _ _ (hcomm S hS S' hS') (hcomm S hS _ (hadj S' hS')))
      (cr _ _ _ (hcomm _ (hadj S hS) S' hS') (hcomm _ (hadj S hS) _ (hadj S' hS')))
  let F : B × Bool → Module.End ℂ H := fun p => reIm p.1.1 p.2
  have hsym : ∀ p, (F p).IsSymmetric := fun p => reIm_isSymmetric _ _
  have hpair : Pairwise (Function.onFun Commute F) := fun p q _ =>
    hc _ (hBA p.1.2) _ (hBA q.1.2) p.2 q.2
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hsym hpair
  have hV := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym
  let E : (B × Bool → ℂ) → Submodule ℂ H := fun α => ⨅ j, (F j).eigenspace (α j)
  have hfinS : ({α | E α ≠ ⊥} : Set (B × Bool → ℂ)).Finite := by
    have : Fintype {α // E α ≠ ⊥} := hint.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
    exact Set.finite_coe_iff.mp (Finite.of_fintype {α // E α ≠ ⊥})
  have hortho : ∀ c ∈ {α | E α ≠ ⊥}, ∀ d ∈ {α | E α ≠ ⊥}, c ≠ d → E c ⟂ E d :=
    fun c _ d _ hcd => hV.isOrtho hcd
  have htop' : ⨆ c ∈ {α | E α ≠ ⊥}, E c = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hint.submodule_iSup_eq_top]
    refine iSup_le fun α => ?_
    by_cases h : E α = ⊥
    · show E α ≤ _
      rw [h]; exact bot_le
    · exact le_biSup E (show α ∈ {α | E α ≠ ⊥} from h)
  obtain ⟨n, b, lab, -, hb⟩ := exists_onb_of_parts_set _ hfinS E hortho htop'
  refine ⟨n, b, fun k => ?_⟩
  have hv : ∀ p, F p (b k) = lab k p • b k := fun p =>
    Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 (hb k) p)

  have hB : ∀ S (hS : S ∈ B), ∃ μ : ℂ, S (b k) = μ • b k := by
    intro S hS
    have e1 : S (b k) + LinearMap.adjoint S (b k) = lab k (⟨S, hS⟩, true) • b k := by
      have := hv (⟨S, hS⟩, true)
      simpa [F, r1] using this
    have e2 : Complex.I • (S (b k) - LinearMap.adjoint S (b k)) = lab k (⟨S, hS⟩, false) • b k := by
      have := hv (⟨S, hS⟩, false)
      simpa [F, r2] using this
    have e2' : S (b k) - LinearMap.adjoint S (b k) = (-Complex.I * lab k (⟨S, hS⟩, false)) • b k := by
      rw [mul_smul, ← e2, smul_smul]
      simp
    have e3 : (2 : ℂ) • S (b k) =
        (lab k (⟨S, hS⟩, true) + -Complex.I * lab k (⟨S, hS⟩, false)) • b k := by
      rw [two_smul, add_smul, ← e1, ← e2']
      abel
    refine ⟨(1 / 2 : ℂ) * (lab k (⟨S, hS⟩, true) + -Complex.I * lab k (⟨S, hS⟩, false)), ?_⟩
    calc S (b k) = (1 / 2 : ℂ) • ((2 : ℂ) • S (b k)) := by rw [smul_smul]; norm_num
      _ = _ := by rw [e3, smul_smul]
  intro T hT
  have hT' : T ∈ Submodule.span ℂ B := hspan ▸ Submodule.subset_span hT
  clear hT
  induction hT' using Submodule.span_induction with
  | mem x hx => exact hB x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨μ₁, h₁⟩ := hx
    obtain ⟨μ₂, h₂⟩ := hy
    exact ⟨μ₁ + μ₂, by rw [LinearMap.add_apply, h₁, h₂, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨μ, h⟩ := hx
    exact ⟨a * μ, by rw [LinearMap.smul_apply, h, smul_smul]⟩
end Formalism.IndefR.EigenDecomposition
