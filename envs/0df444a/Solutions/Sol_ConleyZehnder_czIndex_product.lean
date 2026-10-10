-- Prove2me | solution 1 for ConleyZehnder.czIndex_product
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:20:45.041593+00:00
-- url     : https://prove2.me/submissions/34e7b511-01c7-4748-bd44-a6db2ba00fd4

import Theorems.Thm_ConleyZehnder_rhoHat_diamond
import Theorems.Thm_ConleyZehnder_spStar_rhoHat_increment_eq_zero_of_symm
import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Theorems.Thm_ConleyZehnder_rhoHat_path_continuous
import Theorems.Thm_ConleyZehnder_spStar_exists_path_to_W

open ConleyZehnder Matrix unitInterval

namespace CZ16

variable {n n' n'' : ℕ}

/-! ### The block-diagonal sum `⋄` -/

/-- The index equivalence used by `diamond`. -/
abbrev dE (n' n'' : ℕ) : (Fin n' ⊕ Fin n') ⊕ (Fin n'' ⊕ Fin n'') ≃ Fin (n' + n'') ⊕ Fin (n' + n'') :=
  (Equiv.sumSumSumComm (Fin n') (Fin n') (Fin n'') (Fin n'')).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

theorem diamond_eq (A : Mat n') (B : Mat n'') :
    diamond A B = reindex (dE n' n'') (dE n' n'') (fromBlocks A 0 0 B) := rfl

theorem diamond_mul (A A' : Mat n') (B B' : Mat n'') :
    diamond (A * A') (B * B') = diamond A B * diamond A' B' := by
  simp only [diamond_eq, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem diamond_sub (A A' : Mat n') (B B' : Mat n'') :
    diamond (A - A') (B - B') = diamond A B - diamond A' B' := by
  have h : fromBlocks (A - A') 0 0 (B - B') = fromBlocks A 0 0 B - fromBlocks A' 0 0 B' := by
    ext (i | i) (j | j) <;> simp
  simp only [diamond_eq, reindex_apply, h]
  rfl

theorem diamond_one : diamond (1 : Mat n') (1 : Mat n'') = 1 := by
  simp only [diamond_eq, reindex_apply, fromBlocks_one, submatrix_one_equiv]

theorem diamond_transpose (A : Mat n') (B : Mat n'') :
    (diamond A B)ᵀ = diamond Aᵀ Bᵀ := by
  simp only [diamond_eq, transpose_reindex, fromBlocks_transpose, transpose_zero]

theorem diamond_det (A : Mat n') (B : Mat n'') : (diamond A B).det = A.det * B.det := by
  rw [diamond_eq, det_reindex_self, det_fromBlocks_zero₂₁]

theorem J_submatrix :
    (J₀ (n' + n'')).submatrix (dE n' n'') (dE n' n'') = fromBlocks (J₀ n') 0 0 (J₀ n'') := by
  ext ((a | b) | (c | d)) ((e | f) | (g | h)) <;>
    simp [Matrix.J, fromBlocks, one_apply] <;> simp [Fin.ext_iff] <;> omega

theorem diamond_J : diamond (J₀ n') (J₀ n'') = J₀ (n' + n'') := by
  rw [diamond_eq, ← J_submatrix]
  ext i j
  simp only [reindex_apply, submatrix_apply, Equiv.apply_symm_apply]

theorem diamond_symplectic {A : Mat n'} {B : Mat n''} (hA : IsSymplectic A)
    (hB : IsSymplectic B) : IsSymplectic (diamond A B) := by
  unfold IsSymplectic at *
  rw [SymplecticGroup.mem_iff] at hA hB ⊢
  rw [diamond_transpose, show J (Fin (n' + n'')) ℝ = J₀ (n' + n'') from rfl, ← diamond_J,
    ← diamond_mul, ← diamond_mul]
  exact congrArg₂ diamond hA hB

theorem det_one_sub_diamond (A : Mat n') (B : Mat n'') :
    (1 - diamond A B).det = (1 - A).det * (1 - B).det := by
  rw [← diamond_one, ← diamond_sub, diamond_det]

theorem continuous_diamond {X : Type*} [TopologicalSpace X] {f : X → Mat n'} {g : X → Mat n''}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => diamond (f x) (g x) := by
  simp only [diamond_eq, reindex_apply]
  exact (Continuous.matrix_fromBlocks hf continuous_const continuous_const hg).matrix_submatrix _ _

theorem W_symm {A : Mat n} (h : A = Wplus n ∨ A = Wminus n) : Aᵀ = A := by
  rcases h with rfl | rfl
  · simp [Wplus]
  · simp [Wminus]

/-! ### Glue -/

theorem czIndex_eq_of_value (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) {k : ℤ}
    (hk : IsCZValue ψ k) : czIndex ψ = k := by
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (czValue_existsUnique ψ hψ).unique hex.choose_spec hk

theorem lift_exists (χ : C(unitInterval, Mat n)) (hχ : ∀ t, IsSymplectic (χ t)) :
    (∃ θ, IsArgLift (fun t => rhoHat (χ t)) θ) ∧
      ∀ θ θ', IsArgLift (fun t => rhoHat (χ t)) θ → IsArgLift (fun t => rhoHat (χ t)) θ' →
        θ 1 - θ 0 = θ' 1 - θ' 0 :=
  argLift_exists_increment_unique (rhoHat_path_continuous χ hχ).1 (rhoHat_path_continuous χ hχ).2

/-- Concatenation of two paths of symplectic matrices, and additivity of argument increments. -/
theorem concat (a b : C(unitInterval, Mat n)) (hab : a 1 = b 0)
    (ha : ∀ t, IsSymplectic (a t)) (hb : ∀ t, IsSymplectic (b t)) :
    ∃ c : C(unitInterval, Mat n), c 0 = a 0 ∧ c 1 = b 1 ∧
      (∀ t, (∃ s, c t = a s) ∨ (∃ s, c t = b s)) ∧
      ∀ θa θb, IsArgLift (fun t => rhoHat (a t)) θa → IsArgLift (fun t => rhoHat (b t)) θb →
        ∃ θ, IsArgLift (fun t => rhoHat (c t)) θ ∧
          θ 1 - θ 0 = (θa 1 - θa 0) + (θb 1 - θb 0) := by
  let a' : Path (a 0) (a 1) := ⟨a, rfl, rfl⟩
  let b' : Path (a 1) (b 1) := ⟨b, hab.symm, rfl⟩
  let c : C(unitInterval, Mat n) := (a'.trans b').toContinuousMap
  have hc : ∀ t, (∃ s, c t = a s) ∨ (∃ s, c t = b s) := fun t => by
    show (∃ s, (a'.trans b') t = a s) ∨ (∃ s, (a'.trans b') t = b s)
    rw [Path.trans_apply]
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  have hcs : ∀ t, IsSymplectic (c t) := fun t => by
    rcases hc t with ⟨s, e⟩ | ⟨s, e⟩ <;> rw [e]
    · exact ha s
    · exact hb s
  refine ⟨c, Path.source _, Path.target _, hc, fun θa θb hθa hθb => ?_⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := lift_exists c hcs
  refine ⟨θ, hθ, ?_⟩
  let h₁ : unitInterval → unitInterval := fun u =>
    ⟨(u : ℝ) / 2, by constructor <;> linarith [u.2.1, u.2.2]⟩
  let h₂ : unitInterval → unitInterval := fun u =>
    ⟨((u : ℝ) + 1) / 2, by constructor <;> linarith [u.2.1, u.2.2]⟩
  have hh₁ : ∀ u, c (h₁ u) = a u := fun u => by
    show (a'.trans b') _ = _
    rw [Path.trans_apply, dif_pos (show ((u : ℝ) / 2) ≤ 1 / 2 by linarith [u.2.2])]
    show a _ = a u
    congr 1
    exact Subtype.ext (show (2 : ℝ) * ((u : ℝ) / 2) = u by ring)
  have hh₂ : ∀ u, c (h₂ u) = b u := fun u => by
    show (a'.trans b') _ = _
    rw [Path.trans_apply]
    split_ifs with hle
    · have hle' : ((u : ℝ) + 1) / 2 ≤ 1 / 2 := hle
      have hu : u = 0 := Subtype.ext (by have := u.2.1; simp only [Set.Icc.coe_zero]; linarith)
      subst hu
      rw [← hab]
      show a _ = a 1
      congr 1
      apply Subtype.ext
      norm_num [h₂]
    · show b _ = b u
      congr 1
      exact Subtype.ext (show (2 : ℝ) * (((u : ℝ) + 1) / 2) - 1 = u by ring)
  have hh₁c : Continuous h₁ := by fun_prop
  have hh₂c : Continuous h₂ := by fun_prop
  have inc₁ : θ (h₁ 1) - θ (h₁ 0) = θa 1 - θa 0 := by
    have l1 : IsArgLift (fun u => rhoHat (a u)) (fun u => θ (h₁ u)) :=
      ⟨hθ.1.comp hh₁c, fun u => by
        show rhoHat (a u) = _
        rw [← hh₁ u]; exact hθ.2 _⟩
    exact (lift_exists a ha).2 _ _ l1 hθa
  have inc₂ : θ (h₂ 1) - θ (h₂ 0) = θb 1 - θb 0 := by
    have l1 : IsArgLift (fun u => rhoHat (b u)) (fun u => θ (h₂ u)) :=
      ⟨hθ.1.comp hh₂c, fun u => by
        show rhoHat (b u) = _
        rw [← hh₂ u]; exact hθ.2 _⟩
    exact (lift_exists b hb).2 _ _ l1 hθb
  have e0 : h₁ 0 = 0 := Subtype.ext (by simp [h₁])
  have em : h₁ 1 = h₂ 0 := Subtype.ext (by simp [h₁, h₂])
  have e1 : h₂ 1 = 1 := Subtype.ext (by norm_num [h₂])
  rw [e0, em] at inc₁
  rw [e1] at inc₂
  linarith

/-- Lifts of `ρ̂` along `⋄` add. -/
theorem lift_diamond (a : C(unitInterval, Mat n')) (b : C(unitInterval, Mat n''))
    (c : C(unitInterval, Mat (n' + n''))) (hc : ∀ t, c t = diamond (a t) (b t))
    {θa θb : unitInterval → ℝ} (ha : IsArgLift (fun t => rhoHat (a t)) θa)
    (hb : IsArgLift (fun t => rhoHat (b t)) θb) :
    IsArgLift (fun t => rhoHat (c t)) (fun t => θa t + θb t) :=
  ⟨ha.1.add hb.1, fun t => by
    show rhoHat (c t) = _
    rw [hc, (rhoHat_diamond _ _).2, show rhoHat (a t) = _ from ha.2 t,
      show rhoHat (b t) = _ from hb.2 t, ← Complex.exp_add]
    push_cast; ring_nf⟩

end CZ16

open CZ16

theorem solution {n' n'' : ℕ} (ψ₁ : C(unitInterval, Mat n')) (hψ₁ : ψ₁ ∈ SP n')
    (ψ₂ : C(unitInterval, Mat n'')) (hψ₂ : ψ₂ ∈ SP n'')
    (ψ : C(unitInterval, Mat (n' + n''))) (hψ : ∀ t, ψ t = diamond (ψ₁ t) (ψ₂ t)) :
    czIndex ψ = czIndex ψ₁ + czIndex ψ₂ := by
  have hSP : ψ ∈ SP (n' + n'') := by
    refine ⟨fun t => ?_, ?_, ?_⟩
    · rw [hψ]; exact diamond_symplectic (hψ₁.1 t) (hψ₂.1 t)
    · rw [hψ, hψ₁.2.1, hψ₂.2.1, diamond_one]
    · rw [hψ, det_one_sub_diamond]; exact mul_ne_zero hψ₁.2.2 hψ₂.2.2
  obtain ⟨k₁, hk₁, -⟩ := czValue_existsUnique ψ₁ hψ₁
  obtain ⟨k₂, hk₂, -⟩ := czValue_existsUnique ψ₂ hψ₂
  rw [czIndex_eq_of_value ψ₁ hψ₁ hk₁, czIndex_eq_of_value ψ₂ hψ₂ hk₂]
  apply czIndex_eq_of_value ψ hSP
  obtain ⟨χ₁, ⟨h10, h1s, h1W⟩, a₁, b₁, ha₁, hb₁, hs₁⟩ := hk₁
  obtain ⟨χ₂, ⟨h20, h2s, h2W⟩, a₂, b₂, ha₂, hb₂, hs₂⟩ := hk₂
  -- `χ₁ ⋄ χ₂`, a path in `Sp*` from `ψ(1)`
  let χ : C(unitInterval, Mat (n' + n'')) :=
    ⟨fun t => diamond (χ₁ t) (χ₂ t), continuous_diamond χ₁.continuous χ₂.continuous⟩
  have hχs : ∀ t, χ t ∈ SpStar (n' + n'') := fun t =>
    ⟨diamond_symplectic (h1s t).1 (h2s t).1, by
      show (1 - diamond (χ₁ t) (χ₂ t)).det ≠ 0
      rw [det_one_sub_diamond]; exact mul_ne_zero (h1s t).2 (h2s t).2⟩
  -- from `χ(1)` to `W±`
  obtain ⟨χ₃, h30, h3s, h3W⟩ := spStar_exists_path_to_W (χ 1) (hχs 1)
  obtain ⟨c, hc0, hc1, hcr, hlift⟩ := concat χ χ₃ h30.symm (fun t => (hχs t).1)
    (fun t => (h3s t).1)
  obtain ⟨⟨θ₃, hθ₃⟩, -⟩ := lift_exists χ₃ fun t => (h3s t).1
  have hz := spStar_rhoHat_increment_eq_zero_of_symm χ₃ h3s
    (by rw [h30]; show (diamond (χ₁ 1) (χ₂ 1))ᵀ = diamond (χ₁ 1) (χ₂ 1); rw [diamond_transpose, W_symm h1W, W_symm h2W])
    (W_symm h3W) θ₃ hθ₃
  obtain ⟨θ, hθ, hθinc⟩ := hlift _ _ (lift_diamond χ₁ χ₂ χ (fun _ => rfl) hb₁ hb₂) hθ₃
  refine ⟨c, ⟨?_, fun t => ?_, ?_⟩, _, θ, lift_diamond ψ₁ ψ₂ ψ hψ ha₁ ha₂, hθ, ?_⟩
  · rw [hc0, hψ, ← h10, ← h20]; rfl
  · rcases hcr t with ⟨s, e⟩ | ⟨s, e⟩ <;> rw [e]
    · exact hχs s
    · exact h3s s
  · rw [hc1]; exact h3W
  · push_cast
    rw [hθinc]
    linarith
