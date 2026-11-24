-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.spec_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:27:51.363719+00:00
-- url     : https://prove2.me/submissions/b63f044f-4c4b-42f6-abc3-9828b80cd7fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_spec_sum_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_spec_iter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (hsmul : ∀ F ∈ 𝓕, ∀ c : ℂ, (fun x => c • F x) ∈ 𝓕)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (hinj : Function.Injective (fun σ => lam σ Y₀))
    (S : X → ι → Submodule ℂ Wq) (hS : ∀ g ∈ G, DirectSum.IsInternal (S g))
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) :
    ∃ dec : ι → X → (Wq →L[ℂ] Wp), (∀ σ, dec σ ∈ 𝓕) ∧ (∀ g ∈ G, J g = ∑ σ, dec σ g) ∧
      (∀ σ Y, ∀ g ∈ G, T Y (dec σ) g = (c g * lam σ Y) • dec σ g) ∧
      ∀ g ∈ G, ∀ σ v, ∃ w ∈ S g σ, dec σ g v = J g w := by
  classical
  have hinjOn : Set.InjOn (fun σ => lam σ Y₀) (Finset.univ : Finset ι) := fun a _ b _ h => hinj h
  have hit := spec_iter 𝓕 G T c hc Y₀ hA lam S heig J hJ
  obtain ⟨dec, hdec⟩ : ∃ dec : ι → X → (Wq →L[ℂ] Wp), ∀ σ x, dec σ x =
      ∑ n ∈ Finset.range ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).natDegree + 1),
        (Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).coeff n •
          ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) x := ⟨_, fun _ _ => rfl⟩
  have hmem : ∀ σ, dec σ ∈ 𝓕 := by
    intro σ
    have hfun : dec σ = fun x => ∑ n ∈ Finset.range
        ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).natDegree + 1),
        (fun n x => (Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).coeff n •
          ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) x) n x := funext (hdec σ)
    rw [hfun]
    exact spec_sum_mem 𝓕 h0 hadd _ _ fun n _ => hsmul _ (hit n).1 _
  have hkey : ∀ σ, ∀ g ∈ G, ∀ τ, ∀ v ∈ S g τ, dec σ g v = if σ = τ then J g v else 0 := by
    intro σ g hg τ v hv
    have h1 : dec σ g v =
        ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).eval (lam τ Y₀)) • J g v := by
      rw [hdec, Polynomial.eval_eq_sum_range, Finset.sum_smul, _root_.sum_apply]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [_root_.smul_apply, (hit n).2 g hg τ v hv, smul_smul]
    rw [h1]
    split_ifs with hστ
    · subst hστ
      have he := Lagrange.eval_basis_self hinjOn (Finset.mem_univ σ)
      rw [he, one_smul]
    · have he := Lagrange.eval_basis_of_ne (v := fun σ => lam σ Y₀) hστ (Finset.mem_univ τ)
      rw [he, zero_smul]
  have htop : ∀ g ∈ G, ∀ v : Wq, v ∈ ⨆ i, S g i := fun g hg v => by
    rw [(hS g hg).submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine ⟨dec, hmem, ?_, ?_, ?_⟩
  · intro g hg
    ext v
    rw [_root_.sum_apply]
    refine Submodule.iSup_induction (S g) (motive := fun v => J g v = ∑ σ, dec σ g v)
      (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      simp only [hkey _ g hg τ w hw, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy, Finset.sum_add_distrib]
  · intro σ Y g hg
    ext v
    rw [_root_.smul_apply]
    refine Submodule.iSup_induction (S g)
      (motive := fun v => T Y (dec σ) g v = (c g * lam σ Y) • dec σ g v) (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      rw [heig (dec σ) (hmem σ) g hg τ w hw Y, hkey σ g hg τ w hw]
      split_ifs with hστ
      · rw [hστ]
      · rw [smul_zero, smul_zero]
    · simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy, smul_add]
  · intro g hg σ v
    refine Submodule.iSup_induction (S g)
      (motive := fun v => ∃ w ∈ S g σ, dec σ g v = J g w) (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      by_cases hστ : σ = τ
      · subst hστ
        exact ⟨w, hw, by rw [hkey σ g hg σ w hw, if_pos rfl]⟩
      · exact ⟨0, zero_mem _, by rw [hkey σ g hg τ w hw, if_neg hστ, map_zero]⟩
    · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
    · rintro x y ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
      exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, map_add, h₁, h₂]⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
