-- Prove2me | solution 1 for ConleyZehnder.czIndex_eq_of_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:42:42.254982+00:00
-- url     : https://prove2.me/submissions/a02c482f-fba4-4c99-8c54-8b2edcbfa596

import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_ConleyZehnder_argLift_square_increment

open ConleyZehnder Matrix unitInterval

namespace CZ10F

variable {n : ℕ}

theorem continuous_complexLinearDet : Continuous fun A : Mat n => complexLinearDet A := by
  have hC : Continuous (complexLinearPart : Mat n → Mat n) := by
    unfold complexLinearPart
    fun_prop
  unfold complexLinearDet
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.toBlocks₁₁,
    Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
  exact (Complex.continuous_ofReal.comp (hC.matrix_elem _ _)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (hC.matrix_elem _ _)))

/-- `ρ̂` is continuous with values in `S¹` along any continuous family of symplectic matrices. -/
theorem rhoHat_cont {X : Type*} [TopologicalSpace X] (g : X → Mat n) (hg : Continuous g)
    (hs : ∀ x, IsSymplectic (g x)) :
    Continuous (fun x => rhoHat (g x)) ∧ ∀ x, ‖rhoHat (g x)‖ = 1 := by
  have hd : Continuous fun x => complexLinearDet (g x) := continuous_complexLinearDet.comp hg
  have hne : ∀ x, complexLinearDet (g x) ≠ 0 := fun x => complexLinearDet_ne_zero _ (hs x)
  refine ⟨?_, fun x => ?_⟩
  · unfold rhoHat
    refine hd.div (Complex.continuous_ofReal.comp hd.norm) fun x => ?_
    exact_mod_cast (norm_ne_zero_iff.2 (hne x))
  · unfold rhoHat
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hne x))]

theorem czIndex_eq_of_value (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) {k : ℤ}
    (hk : IsCZValue ψ k) : czIndex ψ = k := by
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (czValue_existsUnique ψ hψ).unique hex.choose_spec hk

end CZ10F

open CZ10F

theorem solution {n : ℕ} (H : C(unitInterval × unitInterval, Mat n))
    (hH : ∀ s t, IsSymplectic (H (s, t))) (h0 : ∀ s, H (s, 0) = 1)
    (h1 : ∀ s, (1 - H (s, 1)).det ≠ 0)
    (ψ₀ ψ₁ : C(unitInterval, Mat n)) (hψ₀ : ∀ t, ψ₀ t = H (0, t))
    (hψ₁ : ∀ t, ψ₁ t = H (1, t)) :
    czIndex ψ₁ = czIndex ψ₀ := by
  have hSP : ∀ (ψ : C(unitInterval, Mat n)) (s : unitInterval), (∀ t, ψ t = H (s, t)) →
      ψ ∈ SP n := fun ψ s hψ =>
    ⟨fun t => by rw [hψ]; exact hH s t, by rw [hψ]; exact h0 s, by rw [hψ]; exact h1 s⟩
  have hSP0 := hSP ψ₀ 0 hψ₀
  have hSP1 := hSP ψ₁ 1 hψ₁
  obtain ⟨k, hk, -⟩ := czValue_existsUnique ψ₀ hSP0
  rw [czIndex_eq_of_value ψ₀ hSP0 hk]
  obtain ⟨χ₀, ⟨hχ0, hχs, hχW⟩, θ₁, θ₂, hθ₁, hθ₂, hsum⟩ := hk
  apply czIndex_eq_of_value ψ₁ hSP1
  -- `ρ̂` on the square
  obtain ⟨hFc, hF1⟩ := rhoHat_cont (fun p => H p) H.continuous (fun p => hH p.1 p.2)
  let F : C(unitInterval × unitInterval, ℂ) := ⟨fun p => rhoHat (H p), hFc⟩
  have lift : ∀ g : unitInterval → unitInterval × unitInterval, Continuous g →
      (∃ θ, IsArgLift (fun t => F (g t)) θ) ∧ ∀ θ θ', IsArgLift (fun t => F (g t)) θ →
        IsArgLift (fun t => F (g t)) θ' → θ 1 - θ 0 = θ' 1 - θ' 0 := fun g hg =>
    argLift_exists_increment_unique (F.continuous.comp hg) (fun _ => hF1 _)
  obtain ⟨b, hb⟩ := (lift (fun s => (s, 1)) (by fun_prop)).1
  obtain ⟨d, hd⟩ := (lift (fun t => (1, t)) (by fun_prop)).1
  obtain ⟨c₀, hc₀⟩ := (lift (fun s => (s, 0)) (by fun_prop)).1
  have hc : IsArgLift (fun s => F (s, 0)) (fun _ => c₀ 0) := ⟨continuous_const, fun s => by
    show rhoHat (H (s, 0)) = _
    rw [h0 s, ← h0 0]; exact hc₀.2 0⟩
  have ha : IsArgLift (fun t => F (0, t)) θ₁ := ⟨hθ₁.1, fun t => by
    show rhoHat (H (0, t)) = _
    rw [← hψ₀]; exact hθ₁.2 t⟩
  have hsq := argLift_square_increment F hF1 θ₁ b (fun _ => c₀ 0) d ha hb hc hd
  -- the extension of `ψ₁`: back along the top edge, then along `χ₀`
  let e : Path (H (0, 1)) (H (1, 1)) :=
    { toFun := fun s => H (s, 1), continuous_toFun := by fun_prop,
      source' := rfl, target' := rfl }
  let c : Path (H (0, 1)) (χ₀ 1) :=
    { toFun := χ₀, continuous_toFun := χ₀.continuous,
      source' := by rw [hχ0, hψ₀], target' := rfl }
  let χ₁ : C(unitInterval, Mat n) := (e.symm.trans c).toContinuousMap
  have hχ₁s : ∀ t, χ₁ t ∈ SpStar n := fun t => by
    show (e.symm.trans c) t ∈ SpStar n
    rw [Path.trans_apply]
    split_ifs
    · exact ⟨hH _ _, h1 _⟩
    · exact hχs _
  let h₁ : unitInterval → unitInterval := fun u =>
    ⟨(u : ℝ) / 2, by constructor <;> linarith [u.2.1, u.2.2]⟩
  let h₂ : unitInterval → unitInterval := fun u =>
    ⟨((u : ℝ) + 1) / 2, by constructor <;> linarith [u.2.1, u.2.2]⟩
  have hh₁ : ∀ u, χ₁ (h₁ u) = H (σ u, 1) := fun u => by
    show (e.symm.trans c) _ = _
    rw [Path.trans_apply, dif_pos (show ((u : ℝ) / 2) ≤ 1 / 2 by linarith [u.2.2])]
    show H (σ _, 1) = H (σ u, 1)
    congr 3
    exact Subtype.ext (show (2 : ℝ) * ((u : ℝ) / 2) = u by ring)
  have hh₂ : ∀ u, χ₁ (h₂ u) = χ₀ u := fun u => by
    show (e.symm.trans c) _ = _
    rw [Path.trans_apply]
    split_ifs with hle
    · have hle' : ((u : ℝ) + 1) / 2 ≤ 1 / 2 := hle
      have hu : u = 0 := Subtype.ext (by have := u.2.1; simp only [Set.Icc.coe_zero]; linarith)
      subst hu
      rw [hχ0, hψ₀]
      show H (σ _, 1) = H (0, 1)
      congr 3
      apply Subtype.ext
      norm_num [h₂]
    · show χ₀ _ = χ₀ u
      congr 1
      exact Subtype.ext (show (2 : ℝ) * (((u : ℝ) + 1) / 2) - 1 = u by ring)
  have hχ₁sym : ∀ t, IsSymplectic (χ₁ t) := fun t => (hχ₁s t).1
  obtain ⟨hGc, hG1⟩ := rhoHat_cont χ₁ χ₁.continuous hχ₁sym
  obtain ⟨θ', hθ'⟩ := (argLift_exists_increment_unique hGc hG1).1
  -- the two halves of `θ'`
  have hh₁c : Continuous h₁ := by fun_prop
  have hh₂c : Continuous h₂ := by fun_prop
  have inc₁ : θ' (h₁ 1) - θ' (h₁ 0) = -(b 1 - b 0) := by
    have l1 : IsArgLift (fun u => F (σ u, 1)) (fun u => θ' (h₁ u)) :=
      ⟨hθ'.1.comp hh₁c, fun u => by
        show rhoHat (H (σ u, 1)) = _
        rw [← hh₁ u]; exact hθ'.2 _⟩
    have l2 : IsArgLift (fun u => F (σ u, 1)) (fun u => b (σ u)) :=
      ⟨hb.1.comp continuous_symm, fun u => hb.2 (σ u)⟩
    have := (lift (fun u => (σ u, 1)) (by fun_prop)).2 _ _ l1 l2
    simp only [symm_one, symm_zero] at this
    linarith
  have inc₂ : θ' (h₂ 1) - θ' (h₂ 0) = θ₂ 1 - θ₂ 0 := by
    have l1 : IsArgLift (fun u => rhoHat (χ₀ u)) (fun u => θ' (h₂ u)) :=
      ⟨hθ'.1.comp hh₂c, fun u => by
        show rhoHat (χ₀ u) = _
        rw [← hh₂ u]; exact hθ'.2 _⟩
    obtain ⟨hKc, hK1⟩ := rhoHat_cont χ₀ χ₀.continuous (fun t => (hχs t).1)
    exact (argLift_exists_increment_unique hKc hK1).2 _ _ l1 hθ₂
  have e0 : h₁ 0 = 0 := Subtype.ext (by simp [h₁])
  have em : h₁ 1 = h₂ 0 := Subtype.ext (by simp [h₁, h₂])
  have e1 : h₂ 1 = 1 := Subtype.ext (by norm_num [h₂])
  rw [e0, em] at inc₁
  rw [e1] at inc₂
  refine ⟨χ₁, ⟨?_, hχ₁s, ?_⟩, d, θ', ⟨hd.1, fun t => ?_⟩, hθ', ?_⟩
  · show (e.symm.trans c) 0 = _
    rw [Path.source, hψ₁]
  · show (e.symm.trans c) 1 = _ ∨ (e.symm.trans c) 1 = _
    rw [Path.target]; exact hχW
  · show rhoHat (ψ₁ t) = _
    rw [hψ₁]; exact hd.2 t
  · linarith
