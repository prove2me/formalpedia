-- Prove2me | solution 1 for CauchyRiemannIndex.asymptoticCZIndex_eq_czIndex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:19:55.913291+00:00
-- url     : https://prove2.me/submissions/d6781451-4c86-483d-ad9c-faac5bae2513

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_ConleyZehnder_czValue_existsUnique

namespace CauchyRiemannIndex

/-- The restricted fundamental solution of a nondegenerate symmetric loop lies in `SP n`. -/
lemma crj_mem_SP (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hnd : IsNondegenerate S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ψ : C(unitInterval, Mat n)) (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    ψ ∈ ConleyZehnder.SP n := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [hψ]; exact fundamentalSolution_symplectic n S hS.2.2 Ψ hΨ t
  · rw [hψ]; simpa using hΨ.1
  · rw [hψ]; simpa using hnd Ψ hΨ

lemma crj_czIndex_eq_of_isCZValue {n : ℕ} (ψ : C(unitInterval, Mat n))
    (hSP : ψ ∈ ConleyZehnder.SP n) {k : ℤ} (hk : IsCZValue ψ k) : czIndex ψ = k := by
  obtain ⟨k', -, huniq⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (huniq _ hex.choose_spec).trans (huniq _ hk).symm

lemma crj_bridge (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hnd : IsNondegenerate S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ψ : C(unitInterval, Mat n)) (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    asymptoticCZIndex S = czIndex ψ := by
  have hSP := crj_mem_SP n S hS hnd Ψ hΨ ψ hψ
  obtain ⟨k, hk, -⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hk' : IsCZValue ψ k := hk
  rw [crj_czIndex_eq_of_isCZValue ψ hSP hk']
  have hex : ∃ k, IsAsymptoticCZValue S k := ⟨k, Ψ, hΨ, ψ, hψ, hk'⟩
  unfold asymptoticCZIndex
  rw [dif_pos hex]
  obtain ⟨Ψ', hΨ', ψ', hψ', hk''⟩ := hex.choose_spec
  have hΨΨ : Ψ' = Ψ := (fundamentalSolution_existsUnique n S hS.1).unique hΨ' hΨ
  have hψψ : ψ' = ψ := ContinuousMap.ext fun t => by rw [hψ', hψ, hΨΨ]
  rw [hψψ] at hk''
  exact (crj_czIndex_eq_of_isCZValue ψ hSP hk'').symm.trans
    (crj_czIndex_eq_of_isCZValue ψ hSP hk')

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hnd : IsNondegenerate S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ψ : C(unitInterval, Mat n)) (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    asymptoticCZIndex S = czIndex ψ :=
  crj_bridge n S hS hnd Ψ hΨ ψ hψ
