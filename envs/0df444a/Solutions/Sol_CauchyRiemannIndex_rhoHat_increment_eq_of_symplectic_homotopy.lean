-- Prove2me | solution 1 for CauchyRiemannIndex.rhoHat_increment_eq_of_symplectic_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T16:56:59.617588+00:00
-- url     : https://prove2.me/submissions/c87c7aae-9468-4a89-b988-10f9804c00c6

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_ConleyZehnder_rhoHat_path_continuous
import Theorems.Thm_ConleyZehnder_argLift_increment_eq_of_homotopy

open Matrix

namespace CRLRho

variable {n : ℕ}

lemma continuous_complexLinearDet : Continuous (CauchyRiemannIndex.complexLinearDet (n := n)) := by
  unfold CauchyRiemannIndex.complexLinearDet CauchyRiemannIndex.complexLinearPart
  apply Continuous.matrix_det
  have h1 : Continuous fun A : CauchyRiemannIndex.Mat n =>
      (1 / 2 : ℝ) • (A - CauchyRiemannIndex.J₀ n * A * CauchyRiemannIndex.J₀ n) := by fun_prop
  have h11 : Continuous fun A : CauchyRiemannIndex.Mat n =>
      (((1 / 2 : ℝ) • (A - CauchyRiemannIndex.J₀ n * A * CauchyRiemannIndex.J₀ n)).toBlocks₁₁).map
        (fun x : ℝ => (x : ℂ)) :=
    (h1.matrix_submatrix Sum.inl Sum.inl).matrix_map Complex.continuous_ofReal
  have h21 : Continuous fun A : CauchyRiemannIndex.Mat n =>
      (((1 / 2 : ℝ) • (A - CauchyRiemannIndex.J₀ n * A * CauchyRiemannIndex.J₀ n)).toBlocks₂₁).map
        (fun x : ℝ => (x : ℂ)) :=
    (h1.matrix_submatrix Sum.inr Sum.inl).matrix_map Complex.continuous_ofReal
  exact h11.add (h21.const_smul Complex.I)

lemma complexLinearDet_ne_zero {A : CauchyRiemannIndex.Mat n}
    (hA : CauchyRiemannIndex.IsSymplectic A) : CauchyRiemannIndex.complexLinearDet A ≠ 0 := by
  have h := (ConleyZehnder.rhoHat_path_continuous (ContinuousMap.const unitInterval A)
    (fun _ => hA)).2 0
  intro h0
  simp only [ContinuousMap.const_apply] at h
  change ‖CauchyRiemannIndex.rhoHat A‖ = 1 at h
  simp [CauchyRiemannIndex.rhoHat, h0] at h

end CRLRho

namespace CauchyRiemannIndex

open CRLRho

theorem rhoHat_increment_eq_of_symplectic_homotopy_aux {n : ℕ}
    (Φ : C(unitInterval × unitInterval, Mat n)) (hs : ∀ p, IsSymplectic (Φ p))
    (h0 : ∀ s, Φ (s, 0) = Φ (0, 0)) (h1 : ∀ s, Φ (s, 1) = Φ (0, 1)) (θ θ' : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (Φ (0, t))) θ)
    (hθ' : IsArgLift (fun t => rhoHat (Φ (1, t))) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 := by
  have hd : Continuous fun p => complexLinearDet (Φ p) :=
    continuous_complexLinearDet.comp Φ.continuous
  have hc : Continuous fun p => rhoHat (Φ p) := by
    unfold rhoHat
    refine hd.div (Complex.continuous_ofReal.comp hd.norm) fun p => ?_
    exact_mod_cast norm_ne_zero_iff.2 (complexLinearDet_ne_zero (hs p))
  have hn : ∀ p, ‖rhoHat (Φ p)‖ = 1 := fun p => by
    unfold rhoHat
    have := complexLinearDet_ne_zero (hs p)
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 this)]
  exact ConleyZehnder.argLift_increment_eq_of_homotopy ⟨fun p => rhoHat (Φ p), hc⟩ hn
    (fun s => by simp only [ContinuousMap.coe_mk]; rw [h0]) (fun s => by
      simp only [ContinuousMap.coe_mk]; rw [h1]) θ θ' hθ hθ'

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution {n : ℕ}
    (Φ : C(unitInterval × unitInterval, Mat n)) (hs : ∀ p, IsSymplectic (Φ p))
    (h0 : ∀ s, Φ (s, 0) = Φ (0, 0)) (h1 : ∀ s, Φ (s, 1) = Φ (0, 1)) (θ θ' : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (Φ (0, t))) θ)
    (hθ' : IsArgLift (fun t => rhoHat (Φ (1, t))) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 :=
  CauchyRiemannIndex.rhoHat_increment_eq_of_symplectic_homotopy_aux Φ hs h0 h1 θ θ' hθ hθ'
